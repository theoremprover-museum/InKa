;;; -*- Syntax: Common-lisp; Mode : Lisp; Base: 10; Package: INKA; -*-


;;; the original datastructure-module is splitted into three disjunct modules:
;;;
;;; a) datastructure  (DA) : this module contains all operations on abstact datatypes as terms, symbols etc.
;;; b) database       (DB) : this module maintains the actual database. E.g the lists of all gterms representing
;;;                          the set of axioms or all function symbols occurring inside the axioms.
;;; c) predefinitions (DP) : this module initializes the database by some predifined functions and predicates.
;;;                          axioms are inserted into the database.

;;; Changes:
;;; =======
;;; 20.08.1996 : DP=INT.INTEGER.CREATE geaendert (Serge)

(in-package :inka)


;;;;;**********************************************************************************************************
;;;;;
;;;;;  D A T A S T R U C T U R E
;;;;;  =========================
;;;;;
;;;;;**********************************************************************************************************


(DEFVAR DA*VARIABLE.COUNTER 0)
(DEFVAR DA*FUNCTION.COUNTER 0)

(DEFVAR DA*COLOUR.COUNTER 0)
(DEFVAR DA*COLOUR.FADED 'FADE)

(DEFVAR DA*GTERM.COLOUR.PRINTING NIL)


;;;;;=========================================================================================================
;;;;;
;;;;;  Chapter 1
;;;;;  ---------
;;;;;
;;;;;  Definition of the abstract datatypes.
;;;;;
;;;;;=========================================================================================================

;;;;;--------------------------------------------------------------------------------------------------------------------
;;;;;
;;;;; Section 1.1
;;;;;
;;;;; Definition of datatypes for sorts, functions and predicates
;;;;;
;;;;;--------------------------------------------------------------------------------------------------------------------


(DEFSTRUCT (DA*OBJECT (:CONC-NAME DA-OBJECT.))
  
  ;;; \verb$DA-Object.$ is the basic datastructure to represent sorts, variables, functions or predicates
  
  PNAME                                 ; name of the object which is a string
  ATTRIBUTES                            ; a property-list 
  DEFINING.INPUT                        ; a reference to an input-object of the deduction module. This input-object represents
					; the user entry which caused the introduction of this object.
  )


(DEFSTRUCT (DA*SORT (:CONC-NAME DA-SORT.) (:INCLUDE DA*OBJECT) (:PRINT-FUNCTION DA=SORT.PRINT))
  
  ;;; \verb$DA-SORT.$ is the datastructure to represent sorts (or datastructures) wrt the order-sorted
  ;;; calculus. In contrast to the ordinary order-sorted approach the sort lattice has to be a tree.
  ;;; Hence weakening of variables during unification is not needed.
  ;;;
  ;;; Following attributes are known and maintained globally for datatype \verb$DA-SORT$
  ;;; \begin{itemize}
  ;;; \item \verb$STRUCTURE$       : sort is term-created
  ;;; \item \verb$FREE.STRUCTURE$  :  the unique-factorization property holds, e.g. each object has a unique syntactical representation
  ;;; \item \verb$DISJUNCT.RANGE$  :  the range of the constructor-functions are pairwise disjunct.
  ;;; \item \verb$GENERIC$         :  parameter for a sort.
  ;;; \end{itemize}

  ALL.SUBSORTS                          ; the transitive closure of all subsorts of sort.
  ALL.SUPERSORTS                        ; the transitive closure of all supersorts of sort.
  DIRECT.SUBSORTS                       ; the subsorts of sort
  DIRECT.SUPERSORTS                     ; the supersorts of sort
  CONSTRUCTOR.FCTS                      ; a list of all contructor functions
  SELECTOR.FCTS                         ; a list of lists of selector functions. Each element of this list
					; corresponds to an element of \verb$CONSTRUCTOR.FCTS$ and represents
					; whose selector-functions.
  BASE.SORTS                            ; a list of all base sorts of sort
  INDEX.FCTS                            ; a list of selector functions of \verb$CONSTRUCTOR.FCTS$. The n-th
					; element of this list corresponds to the n-th element of \verb$CONSTRUCTOR.FCTS$.
  EXAMPLES                              ; a list of ground constructor-terms representing special elements of the sort
  MODIFIERS                             ; a list of modifers like $\Phi \to x = t$ with $x$ of this sort.
  )


(DEFSTRUCT (DA*SYMBOL (:INCLUDE DA*OBJECT) (:CONC-NAME DA-SYMBOL.))

  ;;; \verb$DA-SYMBOL.$ is the datastructure to represent variables, functions or predicates

  SORT                                  ; the range sort of the symbol. In case of predicates this slot
					; will not be used.
  )


(DEFSTRUCT (DA*VARIABLE (:CONC-NAME DA-VARIABLE.) (:INCLUDE DA*SYMBOL) (:PRINT-FUNCTION DA=VARIABLE.PRINT))

  ;;; \verb$DA-VARIABLE.$ is the datastructure to represent variables.
  
  BINDING                               ; slot used by the unification module in order to store the
					; bindings of a variable. Don't use this slot outside the
					; unification while using the UNI-module.
  EXPANSION                             ; slot used by the unification module for internal use.
					; Don't use this slot outside the unification while using the UNI-module.
  )


(DEFSTRUCT (DA*PREFUN (:CONC-NAME DA-PREFUN.) (:INCLUDE DA*SYMBOL))

  ;;; \verb$DA-PREFUN.$ is the datastructure to represent functions or predicates
  
  DOMAIN.SORTS                          ; list of all its domain sorts (\verb$DA-SORT.$)
  ARITY                                 ; number of its arguments
  DEFINITION                            ; in case of a-functions the gterm corresponding to the definition
  DEFINING.SYMBOLS                      ; a list of prefuns used to define this predicate or function
  WFO.SUGGESTED                         ; a list of \verb$DA-WFOSUG.$ denoting the suggested induction orderings
                                        ; of this predicate or function.
  LISPFCT                               ; an atom denoting the lisp-function corresponding to this predicate or function.
  FORMAL.PARAMETERS                     ; a list of variables denoting the formal parameters in the definition
  DATABASE                              ; 
  MODIFIERS                             ;
  REC.POSITIONS                         ; a list of numbers denoting the recursive positions of function
  )


(DEFSTRUCT (DA*FUNCTION (:CONC-NAME DA-FUNCTION.) (:INCLUDE DA*PREFUN) (:PRINT-FUNCTION DA=FUNCTION.PRINT))

  ;;; \verb$DA-FUNCTION.$ is the datastructure to represent functions
  
  ARG.LIMITED                           ; ?
  SKOLEM				; T, iff the function is a skolem function
  )


(DEFSTRUCT (DA*PREDICATE (:CONC-NAME DA-PREDICATE.) (:INCLUDE DA*PREFUN) (:PRINT-FUNCTION DA=PREDICATE.PRINT))

  ;;; \verb$DA-PREDICATE.$ is the datastructure to represent predicates
  
  )


(DEFSTRUCT (DA*XVARIABLE (:CONC-NAME DA-XVARIABLE.) (:print-function da=xvariable.print))

  ;;; \verb$DA-XVARIABLE.$ is the datastructure to represent colour variables

  EXPANSION                             ; slot used by the unification module for internal use.
					; Don't use this slot outside the unification while using the UNI-module.
  BINDING                               ; slot used by the unification module for internal use.
					; Don't use this slot outside the unification while using the UNI-module.
  NAME                                  ; name of the colour-variable
  )



;;;;;--------------------------------------------------------------------------------------------------------------------
;;;;;
;;;;; Section 1.2
;;;;;
;;;;; Definition of datatypes for formula, literals and terms
;;;;;
;;;;;--------------------------------------------------------------------------------------------------------------------


;;; Hierarchy of abstract datatypes denoting formulas or parts of them
;;; ------------------------------------------------------------------
;;;
;;;
;;;                              GTERM
;;;                                |
;;;                      -----------------------------------
;;;                     |                      |           |
;;;                   TERM                  FORMULA     LITERAL
;;;



(DEFSTRUCT (GTERM (:CONC-NAME DA-GTERM.) (:PRINT-FUNCTION DA=GTERM.PRINT))

  ;;; \verb$DA-GTERM.$ is the datastructure to represent terms and formulas. In general
  ;;; this datastructure is used for terms and normalized formulas, i.e. without equivalence,
  ;;; implication, negation, and quantifiers.
  
  SYMBOL                                ; In case of a formula either a junction, a quantifier or a predicate.
					; In case of a literal the predicate symbol and in case of a term
					; either a variable or a function symbol.
  TERMLIST                              ; In case of a junction a list of formulas, in case of a quantification
                                        ; a list of two elements: a variable (denoting the quantified variable)
					; and a formula. In case of a literal or a term a list of terms.
  COLOURS                               ; a property-list indicating the colours of a formula. This is only
					; used for literals and terms.
  PNAME                                 ; the name of a formula or literal
  ATTRIBUTES                            ; a property-list for several informations
  )


(DEFSTRUCT (TERM (:CONC-NAME DA-TERM.) (:INCLUDE GTERM) (:PRINT-FUNCTION DA=TERM.PRINT))

  ;;; \verb$DA-TERM.$ is the datastructure to represent terms.

  )


(DEFSTRUCT (FORMULA (:CONC-NAME DA-FORMULA.) (:INCLUDE GTERM) (:PRINT-FUNCTION DA=FORMULA.PRINT))

  ;;; \verb$DA-FORMULA.$ is the datastructure to represent formulas. In contrast to \verb$DA-GTERM$
  ;;; formulas are used for not normalized formulas, e.g. containing equivalences or quantors.

  )


(DEFSTRUCT (LITERAL (:CONC-NAME DA-LITERAL.) (:INCLUDE FORMULA) (:PRINT-FUNCTION DA=LITERAL.PRINT))

  ;;; \verb$DA-LITERAL.$ is the datastructure to represent literals.
  
  SIGN                                  ; a symbol of type \verb$DA-SIGN$ indicating whether the
					; literal is negated or not.
  )


(DEFSTRUCT (ATTRIBUTE (:CONC-NAME DA-ATTRIBUTE.))

  ;;; \verb$DA-LITERAL.$ is the datastructure to represent attributes of functions or predicates,
  ;;; like associativity or commutativity.
  
  NAME                                  ; the name of the attribute e.g. associative
  ARGUMENTS
  JUSTIFICATION
  COMMENT
  CONDITIONS
  DEFINING.INPUT)


(DEFSTRUCT (DA*MODFRAME (:CONC-NAME DA-MODFRAME.) (:PRINT-FUNCTION DA=MODFRAME.PRINT))

  ;;; \verb$DA-MODFRAME.$ is the datastructure to represent the basic informations of deduction rules,
  ;;;  such as conditional equations or conditional implications.
  
  INPUT                                 ; the left hand side of the rule
  VALUE                                 ; the right hand side of the rule
  CONDITION                             ; a list of gterms representing the conditions of the rule
  PNAME                                 ; name of the modifier.
  GTERM                                 ; the original gterm
  TAF                                   ; the term-access-function to input
  )


(DEFSTRUCT (DA*MODIFIER (:CONC-NAME DA-MODIFIER.) (:PRINT-FUNCTION DA=MODIFIER.PRINT))

  ;;; \verb$DA-MODIFIER.$ is the datastructure to represent deduction rules, such as
  ;;; conditional equations or conditional implications.
  
  INPUT.TAF                             ; a term-access function for \verb$INPUT$ denoting that subterm
					; which causes the classification of this rule. 
  ATTRIBUTES                            ; property-list for several informations.
  MODFRAME                              ; the appropriate modifier rule 
  )


(DEFSTRUCT (DA*COLOURED.MODIFIER (:CONC-NAME DA-CMODIFIER.) (:INCLUDE DA*MODIFIER))

  ;;; \verb$DA-CMODIFIER.$ is used to store the coloured versions of modifiers.
  
  SOLUTION                              ; an indicator for the colour-list
  VALUE.TAF				; term-access-function denoting a subterm in \verb$VALUE$
  )


(DEFSTRUCT (WFO (:CONC-NAME DA-WFO.))

  ;;; The structure \verb$DA-WFO$ represents well--founded orderings (wfos) which are
  ;;; obtained from the terminating functions and predicates. With every function $f$ a list of
  ;;; suggested wfos is associated, the list's elements are objects of type \verb$DA-WFOSUG$,
  ;;; The wfos in $f$'s list are
  ;;; termination orderings of $f$, for example minus's list contains two wfos, since it terminates
  ;;; on its first or its second argument independently. The datastructure \verb$DA-WFOSUG$ connects
  ;;; the wfo with the function definition: A \verb$DA-WFOSUG$ structure contains exactly one wfo
  ;;; structure and some additional information to match the ordering's domain with some sublist of
  ;;; the function's formal parameters
  ;;;
  ;;; \noindent{\bf An example WFO}
  ;;;
  ;;; This is the wfo computed from the \verb$quotient$ function defined in the previous subsection. The
  ;;; value of the \verb$TREE$ slot is abbreviated, it is the wfo--tree shown above.
  ;;;
  ;;; \vspace{3mm}
  ;;;
  ;;; \begin{verbatim}
  ;;;   PARAMETERS: & (x18 x19)
  ;;;   TREE: & (TREE ...)
  ;;;   CHANGEABLES: & (x18)
  ;;;   ATTRIBUTES: & NIL
  ;;; \end{verbatim}
  ;;;
  ;;; \vspace{3mm}
  ;;;
  ;;; The wfo is defined on the two--dimensional domain ${\tt nat} \times {\tt nat}$, its elements are denoted
  ;;; by the pair \verb$(x18 x19)$. The only changeble variable is {\tt x18}, because it is the only variable
  ;;; mentioned in some substitution in the wfo--tree.
  ;;;

  PARAMETERS                            ; The definition of $\prec$ is by cases, saying that
					; a $n$--tuple $(x_1,\ldots,x_n)$ has a certain predecessor
					; $(\sigma_1(x_1),\ldots,\sigma_n(x_n))$ if certain conditions are
					; fulfilled. \verb$PARAMETERS$ is the list of variables $(x_1,\ldots,x_n)$
					; denoting some element of $D_1 \times \cdots \times D_n$. The
					; variables in this list are exactly those mentioned by the list
					; representing the tree in the \verb$TREE$ slot. \verb$PARAMETERS$ is used to
					; connect these variables to the arguments of functions when using
					; $\prec$ to compute induction formulae or when viewing $\prec$
					; as termination ordering of the function $\prec$ was computed from.
  CASE.PARAMETERS                       ; A list of parameters which do not belong to the well-founded ordering
                                        ; but which are used to create additional case-splits during induction
  TREE                                  ; This slot contains the definition by cases mentioned
					; above. The tree defines the conditions to be fulfilled
					; by $(x_1,\ldots,x_n)$ to have a predecessor and substitutions for
					; some of the $x_i$ defining how to compute the predecessor.
					;  
					; \noindent{\bf Syntax of wfo--trees}
					; 
					; Trees are built by two kinds of datastructures:
					; \begin{description}
					;   \item [nodes] are either inner nodes or leaf nodes. The former are
					;         represented by lists of the form {\tt (TREE {\sf
					;         subtree-1 subtree-2 $\ldots$})}, where {\sf subtree-1}
					;         and {\sf subtree-2} etc.\ are {\bf edges}. The latter are lists of
					;         the form {\tt (PRED.SET {\sf subst1 ...})}. The cdr of this list
					;         consists of substitutions or is empty. Each substitution is a list
					;         of the form: the variable to substitute for and a term (a GTERM),
					;         another variable and another term etc, eg.\ {\tt (PRED.SET (x1 s(0)
					;         x2 s(s(0))) (x1 0))}.
					;   \item [edges] are made up of two--element lists: The first element
					;         is the node reached by this edge and the second is the edge--label
					;         which is a formula (represented by a GTERM).
					; \end{description}
					; The value of the \verb$TREE$-slot of the wfo-structure is the root node of the
					; wfo--tree.
					;
					; \noindent{\bf Semantics of wfo--trees}
					;
					; The wfo--tree defines which elements of the ordering's domain possess
					; a predecessor and which elements do not. The substitutions of a leaf
					; node $N$ of the wfo--tree describe how to compute the predecessors of those
					; elements fulfilling the conjunction of the formulae\footnote{
					;   The edge labels are GTERMS, therefore the formulae are implicitly
					;   negated. Thus the conjunction of the negated labels is meant.}
					; which are edge--labels
					; on the path from the root to $N$. For those leafs with no substitutions
					; there are no predecessors.
					;
					; There is a close relationship between wfo--trees and relation descriptions,
					; of Walther for the latter. A path in the wfo--tree from the
					; root to some Leaf $N$ which defines some substitutions corresponds closely
					; to the atomic relation description with the same set of substitutions and
					; with a range formula which is equivalent to the conjunction of the formulae
					; labeling the edges.
					;
					; \noindent{\bf An example wfo--tree for \verb$quotient$}
					;
					; The following wfo--tree denotes the termination ordering of the function
					; \begin{verbatim}
                                        ; function quotient(x,y):nat =
					;   if y = 0 then 0
					;   if not y = 0 and x < y then x
					;   if not y = 0 and not x < y then
					;                    s(quotient(minus(x, y), y))
					; \end{verbatim}
					; where \verb$minus$ and \verb$<$ are defined as usual.
					;
					; \begin{verbatim}
					; (TREE = ((PRED.SET) x19 =/= 0 )
					;         ((TREE ((PRED.SET) Not Lt(x18 x19) )
					;	         ((PRED.SET (x18  minus(x18 x19)))
					;                 Lt(x18 x19)))
					;	    x19 =/= s(p(x19))))
					; \end{verbatim}
					;
  CHANGEABLES                           ; This is the sublist of \verb$PARAMETERS$ lacking those
					; variables which are never changed when computing the predecessor,
					; i.e.\ those variables never mentioned by any substitution in the
					; tree described above.
  ATTRIBUTES                            ; Three attributes are supported:\hspace*{\fill}\\
					; \verb$FCTS.SUGGESTED$, \verb$GTERMS.SUGGESTED$ and
					; \verb$ALTERNATIVE.CASES$.
					; The values of these attributes are the list of
					; functions and gterms resp.\ which suggested this wfo
					; and a list of literals suggesting further case-analyses
  )


(DEFSTRUCT (WFO.SUGGESTED (:CONC-NAME DA-WFOSUG.))

  ;;; The datastructure \verb$DA-WFOSUG$ is used to connect wfos and the functions which suggested the
  ;;; wfos. The wfos in INKA's database are computed from certain information gathered during the
  ;;; termination proof of some function $f$. Every set of minimal projections suggests a wfo, which
  ;;; corresponds to a domain (and range\footnote{
  ;;;   The edge--labels are not necessarily the conditions used in the definition of $f$, but they
  ;;;   are implied by them. This corresponds to a range generalization which is guaranteed to be
  ;;;   well--founded. Any further range generalization is not likely to be well--founded since the
  ;;;   condition has been necessary in the termination proof.})
  ;;; generalization of $f$'s computation ordering. These wfos are stored with the function or
  ;;; predicate in the \verb$WFO.SUGGESTED$ slot of the \verb$DA-PREFUN$ datastructure.
  ;;; 
  ;;; \noindent{\bf An example \verb$WFO.SUGGESTED$}
  ;;;
  ;;; The following suggested wfo stems from the \verb$quotient$ function defined above.
  ;;; It is the only element of the list of wfos in in the \verb$WFO.SUGGESTED$ slot
  ;;; of \verb$quotient$'s DA-PREFUN structure.
  ;;;
  ;;; . POSITION    (1 2)
  ;;; . WFO:        #S(WFO PARAMETERS (x18 x19) TREE (...)
  ;;; .                    CHANGEABLES (x18)
  ;;; .                    ATTRIBUTES NIL)
  ;;; . ATTRIBUTES: NIL
  ;;;
  ;;; From the POSITIONS slots it is known that the variable x18 corresponds to the first formal
  ;;; parameter of \verb$quotient$ and x19 corresponds to the second. 

  POSITIONS                             ; is a list of integers, which connects the variables used to define the
					; \verb$DA-WFO$ --- those mentioned in the \verb$PARAMETERS$--slot
					; of the \verb$DA-WFO$ structure ---  with the
					; formal parameters in the function's definition. If
					; \verb$POSITIONS$ contains the list $(i_1\;
					; i_2\;\ldots\;i_n)$ and \verb$PARAMETERS$ is 
					; $(x_1\;x_2\;\ldots\;x_n)$ for the WFO then $x_j$
					; corresponds to the function's $i_j^{th}$ formal parameter.
  CASE.POSITIONS                        ; is a list of integers which denote the formal parameters used
                                        ; used in the case analysis of the wfo but not involved in the
					; well-founded ordering
  WFO                                   ; contains the structure \verb$DA-WFO$.
  ATTRIBUTES                            ; contains certain attributes.
  )




;;;;;------------------------------------------------------------------------------------------------------


(DEFUN DA-RESET ()

  ;;; Effect:  resets the global counter of the datastructure-module
  ;;; Value:   undefined

  (SETQ DA*FUNCTION.COUNTER 0)
  (SETQ DA*VARIABLE.COUNTER 0)
  (SETQ DA*COLOUR.COUNTER 0))



;;;;;
;;;;;========================================================================================================
;;;;; Chapter 2
;;;;; ---------
;;;;;
;;;;; Functions to handle the datatype sign
;;;;;========================================================================================================


;;; Definition of possible signs of a literal

(DEFCONSTANT DA*SIGN.MINUS '-)
(DEFCONSTANT DA*SIGN.PLUS '+)


(DEFMACRO DA-SIGN.PLUS ()

  ;;; Value:  the sign symbol plus

  `DA*SIGN.PLUS)


(DEFMACRO DA-SIGN.MINUS ()

  ;;; Value:  the sign symbol minus

  `DA*SIGN.MINUS)


(DEFMACRO DA-SIGN.IS.POSITIVE (SIGN)

  ;;; Edited: 10-jul-80 16:28:56
  ;;; Input:  a sign symbol.
  ;;; Value:  t if the given sign denotes the plus symbol, else nil.

  `(EQ ,SIGN DA*SIGN.PLUS))


(DEFMACRO DA-SIGN.IS.NEGATIVE (SIGN)

  ;;; edited: 10-jul-80 16:28:56
  ;;; Input:  a sign symbol.
  ;;; Effect: returns value
  ;;; Value:  t if the given sign denotes the minus symbol, else nil.

  `(EQ ,SIGN DA*SIGN.MINUS))


(DEFMACRO DA-SIGN.ARE.EQUAL (SIGN1 SIGN2)

  ;;; Edited: 10-jul-80 16:28:56
  ;;; Input:  two sign symbols.
  ;;; Value:  t if both signs are identic.

  `(EQ ,SIGN1 ,SIGN2))


(DEFMACRO DA-SIGN.OTHER.SIGN (SIGN)

  ;;; Input:  a sign symbol
  ;;; Value:  the complement sign.

  `(COND ((EQ ,SIGN '+) '-) (T '+)))



;;;;;
;;;;;========================================================================================================
;;;;; Chapter 3
;;;;; ---------
;;;;;
;;;;; Functions to handle the datatype sort
;;;;;========================================================================================================


(DEFUN DA-SORT.IS (SYMBOL)

  ;;; Input:  an sexpression
  ;;; Value:  T, if \verb$SYMBOL$ is a sort
  
  (TYPEP SYMBOL 'DA*SORT))


(DEFUN DA-SORT.IS.FREE.STRUCTURE (SORT)

  ;;; Input:  a sort
  ;;; Value:  T, iff sort is a freely generated structure.
  
  (GETF (DA-SORT.ATTRIBUTES SORT) 'FREE.STRUCTURE))


(DEFUN DA-SORT.IS.GENERATED (SORT)

  ;;; Input:  a sort
  ;;; Value:  T, iff sort is a generated structure.
  
  (OR (GETF (DA-SORT.ATTRIBUTES SORT) 'FREE.STRUCTURE)
      (GETF (DA-SORT.ATTRIBUTES SORT) 'NON-FREE)))


(DEFUN DA-SORT.IS.ENUMERATE.STRUCTURE (SORT)

  ;;; Input:  a sort
  ;;; Value:  T, iff sort is a enumerated structure

  (GETF (DA-SORT.ATTRIBUTES SORT) 'ENUMERATED))


(DEFUN DA-SORT.IS.INFINITE (SORT)
  
  ;;; Edited : 25.02.94 by CS
  ;;; Input  : a sort symbol
  ;;; Value  : T, if \verb$SORT$ denotes a sort with infinite range, NIL else

  (OR (AND (DA-SORT.IS.FREE.STRUCTURE SORT)
	   (SOME #'(LAMBDA (FCT)
		     (OR (DA-FUNCTION.IS.REFLEXIVE FCT)
			 (SOME #'DA-SORT.IS.INFINITE (DA-FUNCTION.DOMAIN.SORTS FCT))))
		 (DA-SORT.CONSTRUCTOR.FCTS SORT)))
      (AND (NOT (DA-SORT.IS.FREE.STRUCTURE SORT))
	   (OR (AND (DP-SORT.SET SORT)
		    (DA-SORT.IS.INFINITE (DP-SORT.ELEMENT.TYPE SORT)))
	       (AND (DP-SORT.ARRAY SORT)
		    (OR (DA-SORT.IS.INFINITE (DP-SORT.ENTRY.TYPE SORT))
			(DA-SORT.IS.INFINITE (DP-SORT.INDEX.TYPE SORT))))))))


(DEFUN DA-SORT.CREATE (NAME DIRECT.SUBSORTS)
  
  ;;; Edited: 11-feb-83 09:38:54                           
  ;;; Input:  a string and a list of sorts               
  ;;; Effect: a sort with name \verb$NAME$ is created with direct subsorts \verb$DIRECT.SUBSORTS$
  ;;; Value:  the generated sort.
  
  (MAKE-DA*SORT :PNAME NAME
		:DIRECT.SUBSORTS DIRECT.SUBSORTS
		:DIRECT.SUPERSORTS (LIST (DP-SORT.TOP.LEVEL.SORT))))


(DEFMACRO DA-SORT.FIND.SUPER.SORT (SORTS SUB.SORT)
  
  ;;; input  : a list of sorts and a specific one
  ;;; value  : returns a non-nil value if \verb$SUB.SORT$ is a member of \verb$SORTS$, else NIL.

  `(FIND-IF #'(LAMBDA (SORT) (MEMBER ,SUB.SORT (DA-SORT.ALL.SUBSORTS SORT))) ,SORTS))



(DEFUN DA-SORT.IS.FINITE (SORT)

  ;;; Input:   a sort
  ;;; Value:   T, if \verb$SORT$ consists only of base-constants.

  (AND (OR (GETF (DA-SORT.ATTRIBUTES SORT) 'FREE.STRUCTURE)
	   (GETF (DA-SORT.ATTRIBUTES SORT) 'NON-FREE))
       (NULL (DA-SORT.BASE.SORTS SORT))
       (EVERY #'(LAMBDA (FCT) (NULL (DA-FUNCTION.DOMAIN.SORTS FCT))) (DA-SORT.CONSTRUCTOR.FCTS SORT))))


(DEFMACRO DA-SORT.COMMON.SUBSORTS (SORT1 SORT2)

  ;;; Edited: 11-feb-83 09:35:59                           
  ;;; Input:  two sorts.
  ;;; Value:  returns the reflexive transitive closure of all common subsorts of \verb$SORT1$ and \verb$SORT2$

  `(INTERSECTION (CONS ,SORT1 (DA-SORT.ALL.SUBSORTS ,SORT1)) (CONS ,SORT2 (DA-SORT.ALL.SUBSORTS ,SORT2))))


(DEFUN DA-SORT.HAVE.COMMON.SUBSORTS (SORT1 SORT2)

  ;;; Input:   two sorts.
  ;;; Value:   T, iff both sorts have a common subsort

  (SOME #'(LAMBDA (SORT) (MEMBER SORT (DA-SORT.ALL.SUBSORTS SORT2)))
	(DA-SORT.ALL.SUBSORTS SORT1)))


(DEFMACRO DA-SORT.COMMON.SUPERSORTS (SORT1 SORT2)

  ;;; Input:  two sorts.
  ;;; Value:  returns the reflexive transitive closure of all common supersorts of \verb$SORT1$ and \verb$SORT2$
  
  `(INTERSECTION (CONS ,SORT1 (DA-SORT.ALL.SUPERSORTS ,SORT1))
                 (CONS ,SORT2 (DA-SORT.ALL.SUPERSORTS ,SORT2))))


(DEFMACRO DA-SORT.IS.SUBSORT (SORT SUPERSORT)

  ;;; Edited: 11-FEB-83 16:35:00                           
  ;;; Input:  two sorts.
  ;;; Value:  T, if \verb$SUPERSORT$ is a supersort of \verb$SORT$, which means \verb$SORT$
  ;;;         is a subsort of \verb$SUPERSORT$, else NIL.
                         
  `(MEMBER ,SUPERSORT (DA-SORT.ALL.SUPERSORTS ,SORT)))


(DEFMACRO DA-SORT.IS.SUPERSORT (SORT SUPERSORT)

  ;;; Edited: 11-feb-83 16:35:00
  ;;; Input:  two sorts
  ;;; Value:  T if \verb$SORT$ is a supersort of \verb$SUPERSORT$, else NIL.
                         
  `(MEMBER ,SORT (DA-SORT.ALL.SUPERSORTS ,SUPERSORT)))



(DEFUN DA-SORT.INDEX.TERM (TERM SUBSORT)

  ;;; Input:   a term $t$ and a sort
  ;;; Value:   if \verb$SUBSORT$ is a base sort of the sort of $t$ then returns $f(t)$ where $f$ is the corresponding
  ;;;          index function

  (LET (INDEX.FCT)
    (COND ((SOME #'(LAMBDA (FCT SORT)
		     (COND ((EQ SORT SUBSORT) (SETQ INDEX.FCT FCT))))
		 (DA-SORT.INDEX.FCTS (DA-TERM.SORT TERM))
		 (DA-SORT.BASE.SORTS (DA-TERM.SORT TERM)))
	   (DA-TERM.CREATE INDEX.FCT (LIST TERM))))))


(DEFUN DA-SORT.CONSTRUCTOR.TERM (TERM FUNC)

  ;;; Input:  a term $t$ and a constructor-function $c$.
  ;;; Value:  a term $c(f_1(t) ... f_n(t))$, where $f_i$ are the selector-functions of $c$.

  (DA-TERM.CREATE FUNC 
		  (MAPCAR #'(LAMBDA (SELECTOR) (DA-TERM.CREATE SELECTOR (LIST (DA-TERM.COPY TERM))))
			  (DA-SORT.SELECTORS.OF.CONSTRUCTOR FUNC))))


(DEFUN DA-SORT.CONSTRUCTOR.OF.SELECTOR (FUNC)

  ;;; Input:  a selector- or index-function
  ;;; Value:  the corresponding constructor-function
  
  (SOME #'(LAMBDA (CONSTR SELECTORS)
	    (COND ((MEMBER FUNC SELECTORS)
		   CONSTR)))
	(DA-SORT.CONSTRUCTOR.FCTS (CAR (DA-FUNCTION.DOMAIN.SORTS FUNC)))
	(DA-SORT.SELECTOR.FCTS (CAR (DA-FUNCTION.DOMAIN.SORTS FUNC)))))


(DEFMACRO DA-SORT.SELECTORS.OF.CONSTRUCTOR (FUNC)

  ;;; Input:  a constructor-function $c$
  ;;; Value:  the list of selector-functions of $c$.

  `(LET* ((SORT (DA-SYMBOL.SORT ,FUNC))
	  (POS (POSITION ,FUNC (DA-SORT.CONSTRUCTOR.FCTS SORT))))
	 (COND (POS (NTH POS (DA-SORT.SELECTOR.FCTS SORT))))))


(DEFUN DA-SORT.INDEX.FCT.OF.SORT (SORT INDEX.SORT)

  ;;; Input:  two sorts
  ;;; Value:  an index-function, with range \verb$INDEX.SORT$ and with domain \verb$SORT$

  (FIND-IF #'(LAMBDA (INDEX.FCT) (EQ (DA-SYMBOL.SORT INDEX.FCT) INDEX.SORT))
	   (DA-SORT.INDEX.FCTS SORT)))


(DEFUN DA-SORT.TERM.IS.STRUCTURE (PARAMETER TERM)

  ;;; Input:  two terms
  ;;; Value:  t, if \verb$PARAMETER$ = \verb$TERM$ denotes a match literal without local variables.

  (LET ((SYMBOL (DA-TERM.SYMBOL TERM)))
    (OR (AND (DA-FUNCTION.IS SYMBOL)
	     (DA-SYMBOL.HAS.ATTRIBUTE SYMBOL 'INDEX.FCT)
	     (EQUAL (DA-TERM.TERMLIST TERM) PARAMETER))
	(AND (DA-FUNCTION.IS SYMBOL)
	     (DA-SYMBOL.IS.STRUCTURE SYMBOL)
	     (EVERY #'(LAMBDA (SUB.TERM SELECT.FCT)
			(AND (EQ (DA-TERM.SYMBOL SUB.TERM) SELECT.FCT)
			     (EQUAL (DA-TERM.TERMLIST SUB.TERM) PARAMETER)))
		    (DA-TERM.TERMLIST TERM) (DA-SORT.SELECTORS.OF.CONSTRUCTOR SYMBOL))))))


(DEFUN DA-SORT.CREATE.ALL.STRUCTURE.TERMS (TERM EXCEPTIONS)

  ;;; Input:  a term and a list containing base-constants, index functions and constructor-functions
  ;;; Value:  a list of structure terms of \verb$TERM$ without those constructed with members of \verb$EXCEPTIONS$.
  ;;;         (without local variables)

  (LET ((SORT (DA-TERM.SORT TERM)))
    (NCONC (MAPCAR #'(LAMBDA (INDEX.FCT)
		       (DA-TERM.CREATE INDEX.FCT (LIST (DA-TERM.COPY TERM))))
		   (SET-DIFFERENCE (DA-SORT.INDEX.FCTS SORT) EXCEPTIONS))
	   (MAPCAR #'(LAMBDA (CONSTRUCTOR.FCT)
		       (DA-SORT.CONSTRUCTOR.TERM (DA-TERM.COPY TERM) CONSTRUCTOR.FCT))
		   (SET-DIFFERENCE (DA-SORT.CONSTRUCTOR.FCTS SORT) EXCEPTIONS)))))


(DEFUN DA-SORT.CREATE.ALL.STRUCTURE.TERMS.WITH.VAR (SORT)

  ;;; Input:  a sort
  ;;; Value:  a list of all structure terms of sort \verb$SORT$.
  ;;;         (using local variables)

  (NCONC (MAPCAR #'(LAMBDA (SUB.SORT)
		     (DA-TERM.CREATE (DA-VARIABLE.CREATE SUB.SORT) NIL))
		 (DA-SORT.BASE.SORTS SORT))
	 (MAPCAR #'(LAMBDA (CONSTRUCTOR.FCT)
		     (DA-TERM.CREATE 
		       CONSTRUCTOR.FCT
		       (MAPCAR #'(LAMBDA (SUB.SORT) (DA-TERM.CREATE (DA-VARIABLE.CREATE SUB.SORT) NIL))
			       (DA-FUNCTION.DOMAIN.SORTS CONSTRUCTOR.FCT))))
		 (DA-SORT.CONSTRUCTOR.FCTS SORT))))



(DEFUN DA-SORT.MATCH.VARS.SUBSTITUTION (TERM STRUC.TERM)

  ;;; Input:  a term and a structure term
  ;;; Value:  a substitution (list representation) which replaces the local variables in \verb$STRUC.TERM$ by
  ;;;         selector function expressions and index function expressions applied to \verb$TERM$, 
  ;;; NOTE :  this function works properly only when \verb$TERM$ is a variable

  (LET ((SYMBOL (DA-TERM.SYMBOL STRUC.TERM)))
    (COND ((DA-VARIABLE.IS SYMBOL) 
	   (LIST STRUC.TERM
		 (DA-TERM.CREATE (DA-SORT.INDEX.FCT.OF.SORT (DA-TERM.SORT TERM) (DA-SYMBOL.SORT SYMBOL)) 
				  (LIST TERM))))
	  (T (MAPCAN #'(LAMBDA (SEL.FCT VAR)
			 (LIST VAR (DA-TERM.CREATE SEL.FCT (LIST TERM))))
		     (DA-SORT.SELECTORS.OF.CONSTRUCTOR SYMBOL)
		     (DA-TERM.TERMLIST STRUC.TERM))))))


(DEFUN DA-SORT.GENERATE.EXAMPLES (SORT)
  
  ;;; Edited :  12.8.87 by DH
  ;;; Input  :  a sort 
  ;;; Effect :  generates some example terms of \verb$SORT$, consisting only of base constants and constructor
  ;;;           function applied to these
  ;;; Value  :  Undefined.
  
  (LET (POSSIBLE.OBJ (COUNTER 0))

    (SETF (DA-SORT.EXAMPLES SORT)
	  (MAPCAN #'(LAMBDA (FUNC)
			    (COND ((NULL (DA-FUNCTION.DOMAIN.SORTS FUNC))
				   (LIST (DA-TERM.CREATE FUNC NIL)))))
		  (DA-SORT.CONSTRUCTOR.FCTS SORT)))
    (COND ((SETQ POSSIBLE.OBJ (DA-SORT.BASE.SORTS SORT))
	   (PUSH (CAR (DA-SORT.EXAMPLES (CAR POSSIBLE.OBJ))) (DA-SORT.EXAMPLES SORT))))
    (MAPC #'(LAMBDA (FCT)
		    (COND ((DA-FUNCTION.DOMAIN.SORTS FCT)
			   (DOTIMES (I 3)
				    (PUSH (DA-TERM.CREATE FCT 
							  (MAPCAR #'(LAMBDA (SUBSORT)
									    (INCF COUNTER 4)
									    (COND ((EQ SUBSORT SORT)
										   (CAR (DA-SORT.EXAMPLES SUBSORT)))
										  ((SETQ POSSIBLE.OBJ (DA-SORT.EXAMPLES SUBSORT))
										   (NTH (MOD (+ (MOD I 3) (* I COUNTER))
											     (LENGTH POSSIBLE.OBJ))
											POSSIBLE.OBJ))))
								  (DA-FUNCTION.DOMAIN.SORTS FCT)))
					  (DA-SORT.EXAMPLES SORT))))))
	  (DA-SORT.CONSTRUCTOR.FCTS SORT))))


(DEFUN DA-SORT.EXCEPTION.VALUE (STRUCTURE.SORT)

  ;;; Edited:  30-MAY-88
  ;;; Input:   a sort 
  ;;; Value:   the exception value of \verb$STRUCTURE.SORT$.

  (LET (CONSTR.DEF)
    (COND ((SETQ CONSTR.DEF (FIND-IF #'(LAMBDA (FUNC) (NULL (DA-FUNCTION.DOMAIN.SORTS FUNC)))
				     (DA-SORT.CONSTRUCTOR.FCTS STRUCTURE.SORT)))
	   (DA-TERM.CREATE CONSTR.DEF NIL))
          ((DA-SORT.BASE.SORTS STRUCTURE.SORT)
	   (DA-SORT.EXCEPTION.VALUE (CAR (DA-SORT.BASE.SORTS STRUCTURE.SORT))))
          ((SETQ CONSTR.DEF (FIND-IF #'(LAMBDA (X)
                                         (NOT (MEMBER STRUCTURE.SORT (DA-FUNCTION.DOMAIN.SORTS X))))
                                     (DA-SORT.CONSTRUCTOR.FCTS STRUCTURE.SORT)))
           (DA-TERM.CREATE CONSTR.DEF (MAPCAR #'DA-SORT.EXCEPTION.VALUE (DA-FUNCTION.DOMAIN.SORTS CONSTR.DEF))))
          (T (CAR (DA-SORT.EXAMPLES STRUCTURE.SORT))))))


(DEFUN DA=SORT.PRINT (SORT OUTPUT IGNORE)

  ;;; Input:  a sort, an output stream and the depth of printing.
  ;;; Effect: prints the name of \verb$SORT$ to the \verb$OUTPUT$ stream.
  ;;; Value:  undefined.

  (DECLARE (IGNORE IGNORE))
  (PRINC (DA-SORT.PNAME SORT) OUTPUT))


;;;;;
;;;;;========================================================================================================
;;;;; Chapter 
;;;;; -------
;;;;;
;;;;; Functions to handle the datatype symbol
;;;;;========================================================================================================



(defmacro da-symbol.is (symbol) 

  ;;; Input:  an sexpression
  ;;; Value:  T iff it is of type \verb$DA*SYMBOL*

  `(typep ,symbol 'da*symbol))


(DEFUN DA-SYMBOL.SKOLEM.CONSTANT.IS (SYMBOL)

  ;;; Input:  a symbol
  ;;; Value:  T, if \verb$SYMBOL$ is a skolem constant

  (AND (DA-FUNCTION.IS SYMBOL)
       (DA-PREFUN.IS.CONSTANT SYMBOL)
       (DA-FUNCTION.SKOLEM SYMBOL)))


(DEFUN DA-SYMBOL.ATTRIBUTE.INSERT (SYMBOL ATTRIBUTE VALUE)

  ;;; input  : a function and an attribute
  ;;; effect : inserts \verb$ATTRIBUTE$ into the slot \verb$ATTRIBUTES$ of the \verb$FUNCTION$
  ;;; Value  : undefined.

  (SETF (GETF (DA-SYMBOL.ATTRIBUTES SYMBOL) ATTRIBUTE) VALUE))


(DEFUN DA-SYMBOL.MULTISET.DIFFERENCE (MSET1 MSET2 &OPTIONAL SET)
  
  ;;; Edited    : 28.01.1994
  ;;; Input     : two multisets of symbols.
  ;;; Effect    : see value.
  ;;; Value     : the disagreement multiset, iff \verb$SET$ = NIL. If \verb$SET$ = T then the disagreement multiset as
  ;;;             a set.

  (LET ((RESULT NIL))
       (COND (MSET1
	      (COND ((MEMBER (CAR MSET1) MSET2)
		     (SETQ RESULT (DA-SYMBOL.MULTISET.DIFFERENCE (CDR MSET1) (REMOVE (CAR MSET1) MSET2 :COUNT 1) SET)))
		    (T (SETQ RESULT (CONS (CAR MSET1) (DA-SYMBOL.MULTISET.DIFFERENCE (CDR MSET1) MSET2 SET)))))))
       (COND ((EQ SET T) (SETQ RESULT (REMOVE-DUPLICATES RESULT))))
       RESULT))


(DEFUN DA-SYMBOL.ATTRIBUTE.DELETE (FOO ATTRIBUTE)
  
  ;;; Input :  a function symbol and an attribute
  ;;; Effect:  removes destructivly \verb$ATTRIBUTE$ from the attribute list of \verb$FOO$.
  ;;; Value:   undefined.

  (REMF (DA-SYMBOL.ATTRIBUTES FOO) ATTRIBUTE))


(DEFUN DA-SYMBOL.IS.STRUCTURE (SYMBOL)

  ;;; Input:  a symbol
  ;;; Value:  T, if \verb$SYMBOL$ is either a base-constant, a constructor-function or a constructively
  ;;;         defined sort.

  (FIND 'STRUCTURE (DA-SYMBOL.ATTRIBUTES SYMBOL)))


(DEFUN DA-SYMBOL.HAS.ATTRIBUTE (SYMBOL ATTRIBUTE &optional ARGS)

  ;;; Input:  a sexpr
  ;;; Value:  T, if \verb$SYMBOL$ has the given \verb$ATTRIBUTE$
  ;;; Note:   \verb$ARGS$ is for future use and is still ignored.

  (DECLARE (IGNORE ARGS))
  (LET ((ATTR (GETF (DA-OBJECT.ATTRIBUTES SYMBOL) ATTRIBUTE)))
    (cond ((eq (type-of attr) 'attribute)
	   (cond ((ded-input.is.active (da-attribute.defining.input attr)) attr)))
	  (t attr))))


(DEFUN DA-SYMBOL.OCCURS.IN.GTERM.LITS (SYMBOL GTERM &OPTIONAL TAF)

  ;;; Input:   a symbol, a gterm and a term-access-function
  ;;; Value:   a list of tafs (concatenated with \verb$TAF$) which denote the occurrences of literals
  ;;;          in \verb$GTERM$ containing \verb$SYMBOL$.

  (DA=SYMBOL.OCCURS.IN.GTERM.LITS SYMBOL GTERM (REVERSE TAF)))


(DEFUN DA=SYMBOL.OCCURS.IN.GTERM.LITS (SYMBOL GTERM TAF)

  ;;; Input:   a symbol, a gterm and a reversed term-access-function
  ;;; Value:   a list of tafs (concatenated with \verb$TAF$) which denote the occurrences of literals
  ;;;          in \verb$GTERM$ containing \verb$SYMBOL$.

  (LET ((COUNTER 0) RESULT)
    (COND ((DA-LITERAL.IS GTERM)
	   (COND ((DA-SYMBOL.OCCURS.IN.GTERM SYMBOL GTERM) (LIST NIL))))
	  (T (COND ((EQ SYMBOL (DA-GTERM.SYMBOL GTERM)) (SETQ RESULT (LIST NIL))))
	     (COND ((AND TAF (EQ 'AND (DA-GTERM.SYMBOL GTERM)))
		    (MAPL #'(LAMBDA (TAFS)
				    (SETF (CAR TAFS) (NCONC1 (CAR TAFS) (CAR TAF))))
			  (DA=SYMBOL.OCCURS.IN.GTERM.LITS SYMBOL (NTH (1- (CAR TAF))
								      (DA-GTERM.TERMLIST GTERM))
							  (CDR TAF))))
		   (T (MAPC #'(LAMBDA (SUB.GTERM)
				      (INCF COUNTER)
				      (SETQ RESULT
					    (NCONC (MAPL #'(LAMBDA (TAFS)
								   (SETF (CAR TAFS) (NCONC1 (CAR TAFS) COUNTER)))
							 (DA=SYMBOL.OCCURS.IN.GTERM.LITS SYMBOL SUB.GTERM
											 (COND ((EQ COUNTER (CAR TAF)) (CDR TAF)))))
						   RESULT)))
			    (DA-GTERM.TERMLIST GTERM))
		      RESULT))))))


(DEFUN DA-SYMBOL.OCCURS.MAXIMAL.IN.GTERM (SYMBOL GTERM &OPTIONAL PROTECTED.ARGS)

  ;;; Input:   a symbol and a property list $(f_1 \hbox{nos}_1 ... f_n \hbox{nos}_n)$.
  ;;; Value:   a list of tafs which denote the occurrences of \verb$SYMBOL$ in \verb$TERM$ except those which occur
  ;;;          in the protected arguments of the corresponding symbol $f_i$ denoted by $\hbox{nos}_i$.

  (LET ((COUNTER 0) RESULT FORBIDDEN.ARGS)
    (COND ((EQ SYMBOL (DA-GTERM.SYMBOL GTERM)) (LIST NIL))
	  (T (SETQ FORBIDDEN.ARGS (GETF PROTECTED.ARGS (DA-GTERM.SYMBOL GTERM)))
	     (MAPC #'(LAMBDA (SUB.GTERM)
			     (INCF COUNTER)
			     (COND ((NOT (MEMBER COUNTER FORBIDDEN.ARGS))
				    (SETQ RESULT
					  (NCONC (MAPL #'(LAMBDA (TAFS)
								 (SETF (CAR TAFS) (NCONC1 (CAR TAFS) COUNTER)))
						       (DA-SYMBOL.OCCURS.MAXIMAL.IN.GTERM SYMBOL SUB.GTERM PROTECTED.ARGS))
						 RESULT)))))
		   (DA-GTERM.TERMLIST GTERM))
	     RESULT))))


(DEFUN DA-SYMBOL.OCCURS.IN.GTERM (SYMBOL GTERM &OPTIONAL PROTECTED.ARGS SIGN)

  ;;; Input:   a symbol and a property list $(f_1 \hbox{nos}_1 ... f_n \hbox{nos}_n)$.
  ;;; Value:   a list of tafs which denote the occurrences of \verb$SYMBOL$ in \verb$TERM$ except those which occur
  ;;;          in the protected arguments of the corresponding symbol $f_i$ denoted by $\hbox{nos}_i$.

  (LET ((COUNTER 0) RESULT FORBIDDEN.ARGS)
    (COND ((AND (EQ SYMBOL (DA-GTERM.SYMBOL GTERM))
		(OR (NULL SIGN) (COND ((DA-LITERAL.IS GTERM) (EQ SIGN (DA-LITERAL.SIGN GTERM))))))
	   (SETQ RESULT (LIST NIL))))
    (SETQ FORBIDDEN.ARGS (GETF PROTECTED.ARGS (DA-GTERM.SYMBOL GTERM)))
    (MAPC #'(LAMBDA (SUB.GTERM)
	      (INCF COUNTER)
	      (COND ((NOT (MEMBER COUNTER FORBIDDEN.ARGS))
		     (SETQ RESULT
			   (NCONC (MAPL #'(LAMBDA (TAFS)
					    (SETF (CAR TAFS) (NCONC1 (CAR TAFS) COUNTER)))
					(DA-SYMBOL.OCCURS.IN.GTERM SYMBOL SUB.GTERM PROTECTED.ARGS SIGN))
				  RESULT)))))
	  (DA-GTERM.TERMLIST GTERM))
    RESULT))


(DEFUN DA-SYMBOL.OCCURS.IN.GTERMLIST (SYMBOL GTERMLIST)

  ;;; Input:   a symbol and a list of gterms
  ;;; Value:   a list of tafs which denote the occurrences of \verb$SYMBOL$ in \verb$GTERMLIST$.

  (LET ((COUNTER -1) RESULT)
       (MAPC #'(LAMBDA (GTERM)
		       (INCF COUNTER)
		       (SETQ RESULT
			     (NCONC (MAPL #'(LAMBDA (TAFS)
						    (SETF (CAR TAFS) (NCONC1 (CAR TAFS) COUNTER)))
					  (DA-SYMBOL.OCCURS.IN.GTERM SYMBOL GTERM NIL))
				    RESULT)))
	     GTERMLIST)
       RESULT))


;;;;;
;;;;;========================================================================================================
;;;;; Chapter 
;;;;; -------
;;;;;
;;;;; Functions to handle the datatype variable
;;;;;========================================================================================================


(DEFUN DA-VARIABLE.CREATE (SORT &OPTIONAL PNAME)

  ;;; Input:  a sort.
  ;;; Effect: a new variable with range \verb$SORT$ (with either a new created name
  ;;;         or \verb$PNAME$) and added to the database.
  ;;; Value:  the generated variable.
  
  (MAKE-DA*VARIABLE :sort SORT :pname (cond (PNAME) (t (FORMAT NIL "x~A" (INCF DA*VARIABLE.COUNTER))))))


(DEFMACRO DA-VARIABLE.IS (VAR)

  ;;; Input:   a symbol
  ;;; Value:   T, iff \verb$VAR$ is a variable.

  `(TYPEP ,VAR 'DA*VARIABLE))


(DEFUN DA=VARIABLE.PRINT (VARIABLE OUTPUT IGNORE)

  ;;; Input:   a variable, an output stream and the depth of printing
  ;;; Effect:  prints the name of the \verb$VARIABLE$ on the \verb$OUTPUT$ stream.
  ;;; Value:   undefined.

  (DECLARE (IGNORE IGNORE))
  (FORMAT OUTPUT "~A" (DA-VARIABLE.PNAME VARIABLE)))


;;;;;
;;;;;========================================================================================================
;;;;; Chapter 
;;;;; -------
;;;;;
;;;;; Functions to handle the datatype predfun
;;;;;========================================================================================================



(DEFMACRO DA-PREFUN.IS (OBJECT)

  ;;; Input:  a sexpression
  ;;; Value:  T, iff \verb$OBJECT$ is a predicate or function.

  `(TYPEP ,OBJECT 'DA*PREFUN))

  
(DEFUN DA-PREFUN.IS.RECURSIVE (PREFUN)

  ;;; Input:  a predicate or function
  ;;; Value:  T, if \verb$SYMBOL$ is a function symbol, which is defined with recursion.

  (GETF (DA-SYMBOL.ATTRIBUTES PREFUN) 'REC.POSITIONS))


(DEFMACRO DA-PREFUN.IS.CONSTANT (PREFUN)

  ;;; Input:  a predicate or function
  ;;; Value:  T, iff the \verb$PREFUN$ is a function with null domain sorts.

  `(EQ 0 (DA-PREFUN.ARITY ,PREFUN)))


(DEFUN DA-PREFUN.IS.DECLARED (PREFUN)

  ;;; Input:  a predicate or function
  ;;; Value:  T, if \verb$PREFUN$ was introduced by a declarative definition

  (GETF (DA-SYMBOL.ATTRIBUTES PREFUN) 'DECLARED))


(DEFUN DA-PREFUN.IS.LESS (SYMBOL1 SYMBOL2)

  ;;; Input:  two symbols
  ;;; Effect: \verb$SYMBOL1$ is less than \verb$SYMBOL2$ iff:
  ;;;         \begin{itemize}
  ;;;         \item \verb$SYMBOL1$ is a constructor or selector function and \verb$SYMBOL2$ is not
  ;;;         \item \verb$SYMBOL1$ is used to define \verb$SYMBOL2$
  ;;;         \item \verb$SYMBOL1$ is defined in a sub-specification of \verb$SYMBOL2$
  ;;;         \end{itemize}
  ;;; Value:  T, if \verb$SYMBOL1$ is less than \verb$SYMBOL2$

  (LET ((RANGE1 (COND ((DA-FUNCTION.IS SYMBOL1)
		       (COND ((DA-FUNCTION.SKOLEM SYMBOL1) -2)
			     ((DA-FUNCTION.IS.CONSTRUCTOR SYMBOL1) 0)
			     ((DA-FUNCTION.IS.SELECTOR SYMBOL1) 1)
			     ((DA-FUNCTION.IS.INDEX SYMBOL1) 1)
			     ((DP-PREFUN.IS.PREDEFINED SYMBOL1) 2)
			     (T 3)))
		      ((DA-PREDICATE.IS.EQUALITY SYMBOL1) -1)
		      ((DP-PREFUN.IS.PREDEFINED SYMBOL1) 2)
		      (T 3)))
	 (RANGE2 (COND ((DA-FUNCTION.IS SYMBOL2)
			(COND ((DA-FUNCTION.SKOLEM SYMBOL2) -2)
			      ((DA-FUNCTION.IS.CONSTRUCTOR SYMBOL2) 0)
			      ((DA-FUNCTION.IS.SELECTOR SYMBOL2) 1)
			      ((DA-FUNCTION.IS.INDEX SYMBOL2) 1)
			      ((DP-PREFUN.IS.PREDEFINED SYMBOL2) 2)
			      (T 3)))
		       ((DA-PREDICATE.IS.EQUALITY SYMBOL2) -1)
		       ((DP-PREFUN.IS.PREDEFINED SYMBOL2) 2)
		       (T 3))))
    (COND ((> RANGE2 RANGE1) T)
	  ((> RANGE1 RANGE2) NIL)
	  ((EQ SYMBOL1 SYMBOL2) NIL)
	  ((EQL RANGE1 3)
	   (OR (DA-PREFUN.IS.A.DEFINING.SYMBOL SYMBOL1 SYMBOL2)
	       (LET ((STACK1 (GETF (da-prefun.attributes SYMBOL1) 'expand.stack))
		     (STACK2 (GETF (da-prefun.attributes SYMBOL2) 'expand.stack)))
		 (AND (NOT (equal stack1 stack2))
		      (subsetp stack2 stack1))))))))


(DEFUN DA-PREFUN.IS.A.DEFINING.SYMBOL (PREFUN1 PREFUN2)

  ;;; Input:  two prefuns
  ;;; Value:  T, if \verb$PREFUN1$ is member of the transitive closure of the definition
  ;;;         hierachie of \verb$PREFUN2$.

  (OR (MEMBER PREFUN1 (DA-PREFUN.DEFINING.SYMBOLS PREFUN2))
      (SOME #'(LAMBDA (SUB.PREFUN2)
		(AND (NEQ SUB.PREFUN2 PREFUN2)
		     (DA-PREFUN.IS.A.DEFINING.SYMBOL PREFUN1 SUB.PREFUN2)))
	    (DA-PREFUN.DEFINING.SYMBOLS PREFUN2))))


(DEFUN DA-PREFUN.IS.INDEPENDENT (PREFUN LIST.OF.PREFUNS)

  ;;; Input:  a predicate or function and a list of predicates and functions
  ;;; Effect: see value
  ;;; Value:  T, iff \verb$PREFUN$ is not used to define any symbol of \verb$LIST.OF.PREFUNS$

  (EVERY #'(LAMBDA (SYMBOL)
	     (NOT (DA-PREFUN.IS.LESS PREFUN SYMBOL)))
	 LIST.OF.PREFUNS))


(DEFUN DA-PREFUN.INDEPENDENT.SYMBOLS (PREFUNS)

  ;;; Input:  a list of functions or predicates
  ;;; Value:  a subset of these symbols which are maximal according to the definition hierarchie

  (REMOVE-IF #'(LAMBDA (PREFUN)
		 (NOT (DA-PREFUN.IS.INDEPENDENT PREFUN (REMOVE PREFUN PREFUNS))))
	     PREFUNS))



(DEFUN DA-PREFUN.ARGUMENT.IS.RECURSIVE (PREFUN POS)

  ;;; input  : a predicate or function and a position
  ;;; value  : T, iff the argument of \verb$PREFUN$ specified by \verb$POS$ is recursive

  (MEMBER POS (DA-PREFUN.REC.POSITIONS PREFUN)))
  

(DEFUN DA-PREFUN.MIN.POSITIONS (PREFUN)
  
  ;;; input  : a predicate or function
  ;;; value  : if \verb$PREFUN$ proposes induction schemes, returns for each scheme a list of its recursion
  ;;;          arguments, else returns a dummy

  (COND ((DA-PREFUN.WFO.SUGGESTED PREFUN)
	  (MAPCAR #'(LAMBDA (WFO.SUG) (DA-WFOSUG.POSITIONS WFO.SUG)) (DA-PREFUN.WFO.SUGGESTED PREFUN)))
	(T (LIST (LIST T)))))


(DEFUN DA-PREFUN.DELETE.ENTRY (PREFUN ENTRY)
  
  ;;; Input :  a function symbol and a database-entry
  ;;; Effect:  removes destructivly \verb$ENTRY$ from the database-slot of \verb$SYMBOL$.
  ;;; Value:   undefined.

  (SETF (DA-PREFUN.DATABASE PREFUN)
	(DELETE ENTRY (DA-FUNCTION.DATABASE PREFUN) :COUNT 1)))



;;;;;
;;;;;========================================================================================================
;;;;; Chapter 
;;;;; -------
;;;;;
;;;;; Functions to handle the datatype function
;;;;;========================================================================================================


(DEFUN DA-FUNCTION.CREATE (&OPTIONAL PNAME SORT DOMAIN.SORTS SKOLEM.FLAG ATTRIBUTES)

  ;;; Input:   a name, a sort, a sort-list and a flag.
  ;;; Effect:  generates a function with the given attributes, if
  ;;;          no pname is specified a new one is generated
  ;;; Value:   the generated function.

  (SETQ PNAME (COND ((NULL PNAME) (DA=FUNCTION.CREATE.PNAME DOMAIN.SORTS))
		    (T (STRING PNAME))))
  (LET ((FUNCTION (MAKE-DA*FUNCTION :PNAME PNAME :ATTRIBUTES ATTRIBUTES :SORT SORT
				    :DOMAIN.SORTS DOMAIN.SORTS
				    :ARITY (LENGTH DOMAIN.SORTS) :SKOLEM SKOLEM.FLAG))
	(COUNTER 0))
    (SETF (GETF (DA-FUNCTION.ATTRIBUTES FUNCTION) 'SORT.REFLEXIVE)
	  (MAPCAN #'(LAMBDA (DOM.SORT)
		      (INCF COUNTER)
		      (COND ((DA-SORT.IS.SUBSORT DOM.SORT SORT) (LIST COUNTER))))
		  DOMAIN.SORTS))
    FUNCTION))


(DEFUN DA-FUNCTION.IS (FUNC)

  ;;; Input:  a sexpr.
  ;;; Value:  T, iff \verb$FUNC$ denotes a function.

  (TYPEP FUNC 'DA*FUNCTION))


(DEFMACRO DA-FUNCTION.IS.REFLEXIVE (FUNCTION)
  
  ;;; input  : a function symbol
  ;;; value  : the reflexive argument positions of \verb$FUNCTION$.

  `(GETF (DA-FUNCTION.ATTRIBUTES ,FUNCTION) 'SORT.REFLEXIVE))


(DEFMACRO DA-FUNCTION.IS.INDEX (FOO)
  
  ;;; input  : a function symbol
  ;;; value  : T, iff \verb$FOO$ is an index function 

  `(GETF (DA-FUNCTION.ATTRIBUTES ,FOO) 'INDEX.FCT))


(DEFMACRO DA-FUNCTION.IS.SELECTOR (FOO)
  
  ;;; input  : a function symbol
  ;;; value  : T, iff \verb$FOO$ is a selector function 

  `(GETF (DA-FUNCTION.ATTRIBUTES ,FOO) 'SEL.STRUCTURE))


(DEFMACRO DA-FUNCTION.IS.CONSTRUCTOR (FOO)
  
  ;;; input  : a function symbol
  ;;; value  : T, iff \verb$FOO$ is a constructor function 

  `(GETF (DA-FUNCTION.ATTRIBUTES ,FOO) 'STRUCTURE))


(DEFUN DA-FUNCTION.IS.INJECTIVE (SYMBOL POSITION)
  
  ;;; edited : 01.04.93 by CS
  ;;; input  : a function symbol and a position
  ;;; value  : T iff \verb$SYMBOL$ is injective in the specified position, NIL otherwise

  (MEMBER POSITION (GETF (DA-FUNCTION.ATTRIBUTES SYMBOL) 'INJECTIVE)))


(DEFUN DA-FUNCTION.HAS.DISJUNCT.RANGE (SYMBOL)
  
  ;;; edited : 01.04.93 by CS
  ;;; input  : a function symbol
  ;;; value  : T iff \verb$SYMBOL$ has disjunct range, NIL otherwise

  (GETF (DA-FUNCTION.ATTRIBUTES SYMBOL) 'DISJUNCT.RANGE))


(DEFUN DA-FUNCTION.IS.MONOTONIC (SYMBOL)

  ;;; Input:  a function symbol
  ;;; Value:  T, iff \verb$SYMBOL$ is monotonic, i.e. $\verb@SYMBOL@(t_1,...,t_n) >= t_i$ for
  ;;;         all reflexive argument positions $i$.

  (GETF (DA-FUNCTION.ATTRIBUTES SYMBOL) 'MONOTONIC))


(defun da-function.is.surjective (function)


  (getf (DA-FUNCTION.ATTRIBUTES function) 'surjective))


(DEFUN DA-FUNCTION.CREATE.TERM (FOO)

  ;;; Input:  a function symbol f
  ;;; Value:  a term $f(x_1,..., x_n)$ where $x_i$ are new variables.

  (DA-TERM.CREATE FOO (MAPCAR #'(LAMBDA (SORT) (da-term.create (DA-VARIABLE.CREATE SORT)))
			      (DA-FUNCTION.DOMAIN.SORTS FOO))))


(DEFUN DA=FUNCTION.PRINT (FUNCTION OUTPUT IGNORE)
  
  ;;; Input:   a function-symbol, an output-stream and an integer
  ;;; Effect:  writes the name of \verb$FUNCTION$ to the \verb$OUTPUT$ stream.
  ;;; Value:   undefined.
  
  (DECLARE (IGNORE IGNORE))
  (FORMAT OUTPUT "~A" (DA-FUNCTION.PNAME FUNCTION)))


(DEFMACRO DA=FUNCTION.CREATE.PNAME (ARGLIST)

  ;;; Input:   a list of sorts
  ;;; Value:   a new name for a function-symbol
  
  `(FORMAT NIL (COND (,ARGLIST "SKO~D") (T "C~D")) (INCF DA*FUNCTION.COUNTER)))


(defun da=function.is.surjective (function formal.parameters)

  ;;; Input:  a function symbol and its formal parameters
  ;;; Effect: inserts a property surjective with the indices of the parameteres which
  ;;;         have to be freely instantiated to generate all possible values.

  (let ((definition (da-function.definition function))
	(sort (da-function.sort function)) 
	value vars constructors)
    (cond ((and (da-sort.is.free.structure sort) definition)
	   (setq constructors (da-sort.constructor.fcts sort))
	   (DA-GTERM.DEF.MAP.WITH.CONDS definition 
					#'(lambda (def conditions)
					    (setq value (second (da-literal.termlist def)))
					    (cond ((and (da-function.is (da-term.symbol value))
							(member (da-term.symbol value) constructors))
						   (cond ((null (da-term.termlist value))
							  (setq constructors (remove (da-term.symbol value) constructors))
							  (mapc #'(lambda (gt) 
								    (mapc #'(lambda (new.var)
									      (setq new.var (position new.var formal.parameters))
									      (setq vars (adjoin new.var vars)))
									  (da-gterm.variables gt)))
								conditions)))))))
	   (cond ((null constructors)
		  (setf (getf (da-function.attributes function) 'surjective) vars)))))))



;;;;;
;;;;;========================================================================================================
;;;;; Chapter 
;;;;; -------
;;;;;
;;;;; Functions to handle the datatype predicate
;;;;;========================================================================================================


(DEFUN DA-PREDICATE.CREATE (&OPTIONAL PNAME DOMAIN.SORTS ATTRIBUTES)
  
  ;;;  Edited: 1-feb-82 16:33:57
  ;;;  Input:  a string, a list of sorts and a property-list
  ;;;  Effect: creates a new predicate symbol with the corresponding slots. If
  ;;;          no pname is specified a new one is generated.
  ;;;  Value:  new predicate symbol.
  
  (MAKE-DA*PREDICATE :PNAME PNAME :DOMAIN.SORTS DOMAIN.SORTS
		     :ATTRIBUTES ATTRIBUTES :ARITY (LENGTH DOMAIN.SORTS)))


(DEFUN DA-PREDICATE.IS (PRED)
  
  ;;;  Edited: 12-nov-79 15:03:21
  ;;;  Input:  a predicate
  ;;;  Value:  T, iff \verb$PRED$ is a predicate symbol
  
  (TYPEP PRED 'DA*PREDICATE))

 
(DEFMACRO DA-PREDICATE.EQUALITY ()
  
  ;;; Input:  a predicate
  ;;; Value:  the equality predicate
  
  `(DP-PREDICATE.EQUALITY))


(DEFMACRO DA-PREDICATE.TRUE ()
  
  ;;; Input:  a predicate
  ;;; Value:  the predicate true
  
  `(DP-PREDICATE.TRUE))


(DEFMACRO DA-PREDICATE.FALSE ()
  
  ;;; Input:  a predicate
  ;;; Value:  the predicate false
  
  `(DP-PREDICATE.FALSE))


(DEFMACRO DA-PREDICATE.IS.EQUALITY (PREDICATE)
  
  ;;; Input:  a predicate symbol             
  ;;; Value:  t, if \verb$PREDICATE$ denotes the equality, else nil.
  
  `(eq ,PREDICATE (DP-PREDICATE.EQUALITY)))


(DEFMACRO DA-PREDICATE.IS.TRUE (PREDICATE)
  
  ;;; Input:  a predicate symbol             
  ;;; Value:  t, if \verb$PREDICATE$ denotes true, else nil.
  
  `(EQ ,PREDICATE (DP-PREDICATE.TRUE)))


(DEFMACRO DA-PREDICATE.IS.FALSE (PREDICATE)
  
  ;;; Input:  a predicate symbol             
  ;;; Value:  t, if \verb$PREDICATE$ denotes false, else nil.
  
  `(EQ ,PREDICATE (DP-PREDICATE.FALSE)))


(DEFUN DA-PREDICATE.DECLARE.AS.DELTA.PREDICATE (PREDICATE FUNC POSITION)
  
  ;;; input  : a predicate symbol, a function symbol and an argument position of the function symbol
  ;;; effect : the property of \verb$PREDICATE$ to be a delta predicate of \verb$FUNC$ for position \verb$POS$ is inserted
  ;;;          into the slot \verb$ATTRIBUTES$ of \verb$PREDICATE$.

  (DB-PREDICATE.INSERT PREDICATE)
  (PUSH (CONS FUNC POSITION) (DA-PREDICATE.ATTRIBUTES PREDICATE))
  (PUSH 'DELTA.PREDICATE (DA-PREDICATE.ATTRIBUTES PREDICATE)))


(DEFUN DA-PREDICATE.IS.DELTA.PREDICATE (PREDICATE)
  
  ;;; input  : a predicate symbol
  ;;; value  : if \verb$PREDICATE$ is a delta predicate returns a multiple value :
  ;;;          \begin{enumerate}
  ;;;          \item the function predicate is delta predicate for
  ;;;          \item the argument position of the function predicate is delta predicate for
  ;;;          \end{enumerate}
  
  (LET ((ENTRY (GETF (DA-PREDICATE.ATTRIBUTES PREDICATE) 'DELTA.PREDICATE)))
       (COND (ENTRY (VALUES (CAR ENTRY) (CDR ENTRY))))))


(DEFUN DA=PREDICATE.PRINT (PREDICATE OUTPUT IGNORE)

  ;;; input  : a predicate symbol
  ;;; Effect : prints \verb$PREDICATE$ on the \verb$OUTPUT$ stream
  ;;; Value:   undefined.
  
  (DECLARE (IGNORE IGNORE))
  (PRINC (DA-PREDICATE.PNAME PREDICATE) OUTPUT))


(DEFUN DA-PREDICATE.DEFINITION.BODY (PREDICATE SIGN)

  ;;; Input  : a predicate and a sign
  ;;; Effect : computes out of the definition of P an equivalence for P(..), 
  ;;;          iff the sign is positive; an equivalence 
  ;;;          for NOT P(..), iff the sign is negative.
  ;;; Value  : the gterm representing the equivalence

  (COND ((AND (DA-PREDICATE.IS PREDICATE)
	      (NOT (EQ PREDICATE (DA-PREDICATE.EQUALITY)))
	      (DA-PREDICATE.DEFINITION PREDICATE))
	 (car (da=PREDICATE.DEFINITION.EQUIVALENCES (da-predicate.definition predicate) sign)))))


(DEFUN da=PREDICATE.DEFINITION.EQUIVALENCES (DEF.GTERM SIGN)

  ;;; See da-predicate.definition.body

  (LET (RESULT)
    (COND ((EQUAL (DA-GTERM.SYMBOL DEF.GTERM) 'AND)
	   (COND ((SETQ RESULT (MAPCAN #'(LAMBDA (SUBGTERM)
					   (da=PREDICATE.DEFINITION.EQUIVALENCES SUBGTERM SIGN)) 
				       (DA-GTERM.TERMLIST DEF.GTERM)))
		  (LIST (DA-gterm.CREATE 'OR RESULT)))))
	  ((EQUAL (DA-GTERM.SYMBOL DEF.GTERM) 'OR)
	   (COND ((DA-LITERAL.IS (SETQ RESULT (CAR (DA-GTERM.TERMLIST DEF.GTERM))))
		  (COND ((EQUAL SIGN (DA-LITERAL.SIGN RESULT))
			 (LIST (DA-FORMULA.NEGATE.AND.NORMALIZE 
				(DA-gterm.CREATE 'OR (CDR (DA-GTERM.TERMLIST DEF.GTERM))))))))
		 ((SETQ RESULT (MAPCAN #'(LAMBDA (SUBGTERM)
					   (da=PREDICATE.DEFINITION.EQUIVALENCES SUBGTERM SIGN)) 
				       (BUTLAST (DA-GTERM.TERMLIST DEF.GTERM))))
		  (LIST (DA-gterm.CREATE 'AND 
					   (LIST (DA-gterm.CREATE 'OR RESULT)
						 (DA-FORMULA.NEGATE.AND.NORMALIZE 
						  (CAR (LAST (DA-GTERM.TERMLIST DEF.GTERM)))))))))))))





;;;;;
;;;;;========================================================================================================
;;;;; Chapter 
;;;;; -------
;;;;;
;;;;; Functions to handle to global stack of the taf
;;;;;========================================================================================================


(DEFMACRO DA-TAF.CREATE.ZERO (TAF &optional reverse)
  
  ;;; Edited: 16-FEB-83 16:39:12                           
  ;;; Input:  a term access function               
  ;;; Value:  a new taf specifying the term symbol of the term specified by \verb$TAF$ 
  
  `(CONS (COND (,REVERSE (1+ ,REVERSE)) (t 0))
	 ,TAF))


(DEFMACRO DA-TAF.CREATE.NEXT (TAF &optional reverse)
  
  ;;; Edited: 16-feb-83 16:39:12                           
  ;;; Input:  a term access function denoting a subterm of a termlist.                               
  ;;; Value:  a new term access function denoting the next subterm of the termlist at the same level.
  
  `(CONS (COND (,REVERSE (1- (CAR ,TAF))) (t (1+ (CAR ,TAF))))
	 (CDR ,TAF)))


(DEFMACRO DA-TAF.REPLACE.NEXT (TAF)
  
  ;;; Edited: 16-feb-83 16:39:12                           
  ;;; Input:  a term access function denoting a subterm of a termlist.                               
  ;;; Value:  the term access function denoting the next subterm of the termlist at the same level, changes
  ;;;         the given \verb$TAF$ destructively
  
  `(PROGN (INCF (CAR ,TAF)) ,TAF))


(DEFMACRO DA-TAF.CREATE.LEFT (&OPTIONAL TAF)
  
  ;;; Edited: 16-feb-83 16:39:12                           
  ;;; Input:  none.
  ;;; Value:  a term access function denoting the first term of a termlist.
  
  `(CONS 1 ,TAF))


(DEFMACRO DA-TAF.CREATE.RIGHT (&OPTIONAL TAF)
  
  ;;; Edited: 16-feb-83 16:39:12                           
  ;;; Input:  none.
  ;;; Value:  a term access function denoting the second term of a termlist.
  
  `(CONS 2 ,TAF))


(DEFMACRO DA-TAF.IS.LEFT (TAF)
  
  ;;; Edited: 16-feb-83 16:39:12                           
  ;;; Input:  a term access function                       
  ;;; Value:  t, iff taf denotes the first term of a termlist at toplevel
  
  `(EQUAL ,TAF '(1)))


(DEFMACRO DA-TAF.IS.RIGHT (TAF)
  
  ;;; Edited: 16-feb-83 16:39:12
  ;;; Input:  a term access function                       
  ;;; Value:  t, iff \verb$TAF$ denotes the second term of a termlist at toplevel
  
  `(EQUAL ,TAF '(2)))


(DEFMACRO DA-TAF.TOPLEVEL (TAF)
  
  ;;; Edited at 8-sep-81
  ;;; Input:  a term access function
  ;;; VAlue:  toplevel term access function of the given \verb$TAF$
  
  `(LIST (CAR (LAST ,TAF))))


(DEFMACRO DA-TAF.POSITION (TAF)
  ;;; input  : a term access function at toplevel
  ;;; value  : the corresponding term position
  
  `(CAR ,TAF))


(DEFMACRO DA-TAF.UPPER.SUBTAF (SUBTAF TAF)
  
  ;;; Edited:   4.4.88
  ;;; Input :   two term access functions, where subtaf is the lower part of taf
  ;;; Value :   a term access function denoting the difference of both term access functions, which means
  ;;;           the upper part of \verb$TAF$,  occurring in \verb$SUBTAF$
  
  `(NTHCDR (LENGTH ,SUBTAF) ,TAF))


(DEFUN DA-TAF.IS.SUBTAF (SUBTAF TAF)
  
  ;;; Edited:   4.4.88
  ;;; Input :   two term access functions
  ;;; Value :   T, iff \verb$SUBTAF$ denotes an upper term of the term denoted by \verb$TAF$
  
  (AND (>= (LENGTH TAF) (LENGTH SUBTAF))
       (equal subtaf (nthcdr (- (length taf) (length subtaf)) taf))))



(defun da-taf.botton.tafs (tafs)

  ;;; Edited:   10.2.2001
  ;;; Input :   a list of tafs
  ;;; Effect:   removes all non-independent upper tafs from \verb$TAFS$.

  (remove-if #'(lambda (taf)
		 (some #'(lambda (taf2)
			   (and (not (eq taf2 taf))
				(da-taf.is.subtaf taf taf2)))
		       tafs))
	     tafs))


(DEFMACRO DA-TAF.ARE.EQUAL (TAF1 TAF2)
		  
  ;;; edited    : 02.02.2994
  ;;; input     : two tafs
  ;;; effect    : see value
  ;;; value     : T, iff the two tafs are equal; NIL otherwise.
		  
  `(EQUALP ,TAF1 ,TAF2))


(DEFMACRO DA-TAF.LENGTH (TAF)
  
  ;;; edited    : 02.02.1994
  ;;; input     : a taf
  ;;; value     : the length/depth of \verb$TAF$.

  `(LENGTH ,TAF))


(DEFMACRO DA-TAF.SUPER.TAF (TAF &OPTIONAL STEPS)
  
  ;;; Input :  a term access function and a number of $steps >= 1$
  ;;; Value:   a term access function to the next upper term.
  
  `(NTHCDR (COND (,STEPS) (T 1)) ,TAF))


(DEFUN DA-TAF.COMMON.TAF (TAFS)
  
  ;;; Input:   a list of term access functions which may not be empty !
  ;;; Value:   a taf to the most nested term containing all terms denoted \verb$TAFS$.
  
  (LET (COMMON.TAF)
       (SETQ TAFS (MAPCAR #'(LAMBDA (TAF) (REVERSE TAF)) TAFS))
       (WHILE (AND (CAR TAFS)
		   (EVERY #'(LAMBDA (TAF)
				    (EQ (CAR TAF) (CAAR TAFS)))
			  TAFS))
	      (PUSH (CAAR TAFS) COMMON.TAF)
	      (MAPL #'(LAMBDA (TAFL) (SETF (CAR TAFL) (CDR (CAR TAFL)))) TAFS))
       COMMON.TAF))


(DEFMACRO DA-TAF.DIFFERENT.SIDES (TAF1 TAF2)
  
  ;;; Edited:  15.2.88
  ;;; Input:   two term access functions
  ;;; Value:   T, if both term access functions have different top level selectors
  
  `(NOT (EQUAL (LAST ,TAF1) (LAST ,TAF2))))


(DEFMACRO DA-TAF.COMPOSE.TWO.TAFS (TAF1 TAF2)
  
  ;;; Edited:  15.2.88
  ;;; Input:   two term access functions
  ;;; Value:   a combined taf of both tafs.
  
  `(APPEND ,TAF2 ,TAF1))


(DEFUN DA-TAF.OTHERSIDE (TAF)
  
  ;;; Edited: 11.2.83                                      
  ;;; Input:  a term access function (TAF)                 
  ;;; Value:  if taf is a toplevel function on the first or second element then value is a toplevel   
  ;;;         function denoting the other term (esp. the otherside of an equation), else the value is nil.
  
  (COND ((EQ (CAR TAF) 1) (CONS 2 (CDR TAF)))
	((EQ (CAR TAF) 2) (CONS 1 (CDR TAF)))
	(T NIL)))


(DEFUN DA-TAF.SYMBOL.LIST (TAF GTERM)
  
  ;;; Edited :  10.4.88
  ;;; Input  :  A gterm-access-function and a gterm
  ;;; Value  :  A list of the function and predicate symbols occurring in  \verb$GTERM$ along the way down to the subterm
  ;;;           denoted by \verb$TAF$.
  
  (NREVERSE (MAPCAR #'(LAMBDA (ARG.POS)
			      (PROG1 (DA-GTERM.SYMBOL GTERM)
				     (SETQ GTERM (NTH (1- ARG.POS) (DA-GTERM.TERMLIST GTERM)))))
		    (REVERSE TAF))))


(DEFMACRO DA-TAF.DIFFERENCE.OF.TWO.TAFS (TAF1 TAF2)
  
  ;;; input  : two term access functions
  ;;; value  : the difference between the two tafs where \verb$TAF1$ specifies a subterm of the term
  ;;;          specified by \verb$TAF2$.
  
  `(BUTLAST ,TAF1 (LENGTH ,TAF2)))


(DEFUN DA-TAF.APPLY.FCT (TAF GTERM FCT)
  
  ;;; Edited:  10.3.88
  ;;; Effect:  \verb$FCT$ is destructively applied to the subterm of \verb$GTERM$ accessed by \verb$TAF$.
  ;;; Value :  the changed \verb$GTERM$.
  
  (COND ((NULL TAF) (FUNCALL FCT GTERM))
	(T (PROG1 GTERM
		  (SETQ GTERM (DA-ACCESS (CDR TAF) GTERM))
		  (SETF (NTH (1- (CAR TAF)) (DA-GTERM.TERMLIST GTERM))
			(FUNCALL FCT (NTH (1- (CAR TAF)) (DA-GTERM.TERMLIST GTERM))))))))


(DEFUN DA-TAF.LITERAL.TAF (TAF GTERM)

  ;;; Input:   a term-access-function and a gterm
  ;;; Effect:  computes a sub-taf of \verb$TAF$ which accesses to a literal containing the
  ;;;          subterm of \verb$GTERM$ specified by \verb$TAF$.
  ;;; Value:   the selected literal
 
  (LET (NEW.TAF)
    (SETQ TAF (REVERSE TAF))
    (WHILE (AND TAF (NOT (DA-LITERAL.IS GTERM)))
      (SETQ GTERM (NTH (1- (CAR TAF)) (DA-GTERM.TERMLIST GTERM)))
      (PUSH (POP TAF) NEW.TAF))
  NEW.TAF))
    


(DEFUN DA-TAF.COMPARE (TAF1 TAF2)

  ;;; Input:  two term-access-functions
  ;;; Value:  'left ('right) iff \verb$TAF1$ specifies a subtree which is left (right) of the tree specified by \verb$TAF2$.
  
  (some #'(lambda (arg1 arg2)
	    (cond ((< arg1 arg2) 'left)
		  ((eql arg1 arg2) nil)
		  ((> arg1 arg2) 'right)))
	(reverse taf1) (reverse taf2)))


(DEFUN DA-TAF.IS.TOP.LEVEL (TAF GTERM)

  ;;; Input:   a term-access function and a gterm
  ;;; Value:   T, if \verb$TAF$ is either NIL, denotes a formula or literal, or one side of an negated equation.

  (OR (NULL TAF)
      (LET ((GTERM (DA-ACCESS (CDR TAF) GTERM)))
	(COND ((DA-TERM.IS GTERM) NIL)
	      ((DA-LITERAL.IS GTERM)
	       (AND (DA-SIGN.IS.NEGATIVE (DA-LITERAL.SIGN GTERM))
		    (DA-PREDICATE.IS.EQUALITY (DA-LITERAL.SYMBOL GTERM))))
	      (T T)))))


(DEFUN DA-TAFS.ARE.INDEPENDENT (TAF1 TAF2)
  
  ;;; Edited    : 08.02.1994
  ;;; Input     : two term access functions 
  ;;; Value     : T, iff the tafs are equal or if for each taf, one isn't a subtaf of the other.

  (OR (DA-TAF.ARE.EQUAL TAF1 TAF2)
      (AND (NOT (DA-TAF.IS.SUBTAF TAF1 TAF2))
	   (NOT (DA-TAF.IS.SUBTAF TAF2 TAF1)))))


(DEFUN DA-TAFS.SOME.ARE.INDEPENDENT (TAFS)
  
  ;;; Input:  a list of term-accesss-functions
  ;;; Value:  t, iff the list has only one taf or at least two tafs, where each
  ;;;         isn't a subtaf of the other.

  (AND (OR (EQ (LENGTH TAFS) 1)
	   (SOME #'(LAMBDA (TAF1)
		     (SOME #'(LAMBDA (TAF2)
			       (NOT (OR (DA-TAF.IS.SUBTAF TAF1 TAF2)
					(DA-TAF.IS.SUBTAF TAF2 TAF1))))
			   (REMOVE TAF1 TAFS)))
		 TAFS))
       T))


(DEFMACRO DA-TAF.COLOUR.TAF (TAF GTERM SOLUTION)

  ;;; Input:  a term-access-function, a gterm, and a indicator
  ;;; Effect: see value
  ;;; Value:  a term-access-function for the skeleton (with indicator: \verb$SOLUTION$)
  ;;;         of \verb$GTERM$ denoting the subterm of \verb$GTERM$ specified by \verb$TAF$.
  
  `(DA=TAF.COLOUR.TAF (REVERSE ,TAF) ,GTERM ,SOLUTION))


(DEFUN DA=TAF.COLOUR.TAF (R.TAF GTERM SOLUTION)
  
  ;;; Input:   a reversed access function, a gterm, and a indicator
  ;;; Value:   a term-access-function for the skeleton (with indicator: \verb$SOLUTION$)
  ;;;          of \verb$GTERM$ denoting the subterm of \verb$GTERM$ specified by \verb$R.TAF$.
  
  (COND ((NULL R.TAF) NIL)
	((NOT (DA-COLOUR.IS.FADE (DA-GTERM.COLOUR GTERM SOLUTION)))
	 (NCONC (DA=TAF.COLOUR.TAF (CDR R.TAF) 
				   (NTH (1- (CAR R.TAF)) (DA-GTERM.TERMLIST GTERM))
				   SOLUTION)
		(LIST (CAR R.TAF))))
	(T (DA=TAF.COLOUR.TAF (CDR R.TAF) 
			      (NTH (1- (CAR R.TAF)) (DA-GTERM.TERMLIST GTERM))
			      SOLUTION))))


(DEFUN DA-ACCESS (TAF GTERM)
  
  ;;; Input:  a term-access-function and a gterm
  ;;; Value:  subterm of \verb$GTERM$ accessed by \verb$TAF$.
  ;;; Notice: A fatal error will occur, if no such subterm exists !
  
  (COND ((NULL TAF) GTERM)
	((AND (CONSP TAF) (EQ (CAR TAF) 'COLOUR)) (DA-GTERM.COLOUR GTERM (cdr taf)))
	(T (NTH (1- (CAR TAF)) (DA-GTERM.TERMLIST (DA-ACCESS (CDR TAF) GTERM))))))



(DEFUN da-gterm.taf.is.defined (GTERM TAF)
  
  ;;; Input:  a term-access-function and a gterm
  ;;; Value:  subterm of \verb$GTERM$ accessed by \verb$TAF$.
  ;;; Notice: A fatal error will occur, if no such subterm exists !
  
  (COND ((NULL TAF) GTERM)
	((AND (CONSP TAF) (EQ (CAR TAF) 'COLOUR)) (DA-GTERM.COLOUR GTERM (cdr taf)))
	(T (let ((subterm (DA-gterm.taf.is.defined GTERM (CDR TAF))))
	     (cond ((and subterm (da-gterm.termlist subterm))
		    (NTH (1- (CAR TAF)) (DA-GTERM.TERMLIST subterm))))))))



(DEFUN DA-REPLACE (TAF GTERM NEW.GTERM)
  
  ;;; Input:  a term-access-function and two gterms
  ;;; Effect: the subterm of \verb$GTERM$ accessed by \verb$TAF$ is replaced by \verb$NEW.GTERM$
  ;;; Notice: A fatal error will occur, if no such subterm exists !
  
  (COND ((NULL TAF) NEW.GTERM)
	((AND (CONSP TAF) (EQ (CAR TAF) 'COLOUR))
	 (SETF (GETF (DA-GTERM.COLOURS GTERM) (CDR TAF)) NEW.GTERM) GTERM)
	((CONSP TAF)
	 (SETF (NTH (1- (CAR TAF)) (DA-GTERM.TERMLIST (DA-ACCESS (CDR TAF) GTERM)))
	       NEW.GTERM)
	 GTERM)))


;;;;;
;;;;;========================================================================================================
;;;;; Chapter 
;;;;; -------
;;;;;
;;;;; Functions to handle colours
;;;;;========================================================================================================




(DEFUN DA-XVARIABLE.IS (SEXPR)
  
  ;;; Input:  a sexpression
  ;;; Value:  T, iff \verb$SEXPR$ is a xvariable (colour-variable).
  
  (EQ (TYPE-OF SEXPR) 'DA*XVARIABLE))


(DEFUN DA-COLOUR.CREATE.VARIABLE ()

  ;;; Value:  creates a new xvariable (colour-variable).

  (MAKE-DA*XVARIABLE :NAME (INCF DA*COLOUR.COUNTER)))


(DEFUN DA=XVARIABLE.PRINT (XVAR STREAM DEPTH)

  ;;; Input:  a xvariable, a stream and an integer
  ;;; Effect: prints \verb$XVARIABLE$ on \verb$STREAM$
  ;;; Value:  undefined.
  
  (DECLARE (IGNORE DEPTH))
  (FORMAT STREAM "Col~D" (DA-XVARIABLE.NAME XVAR)))


(DEFUN DA-COLOUR.FADED ()

  ;;; Value:  the context-colour

  DA*COLOUR.FADED)


(DEFUN DA-COLOUR.IS.FADE (COLOUR)
  
  ;;; Input:  a colour
  ;;; Value:  T, if \verb$COLOUR$ is the context-colour
  
  (or (null colour) (EQ COLOUR DA*COLOUR.FADED)))


(DEFUN DA-COLOUR.IS.VARIABLE (COLOUR)
  
  ;;; Input:  a colour
  ;;; Value:  T, if \verb$COLOUR$ is a xvariable
  
  (DA-XVARIABLE.IS COLOUR))


(DEFUN DA-COLOUR.IS.CONSTANT (COLOUR)
  
  ;;; Input:  a colour
  ;;; Value:  T, if \verb$COLOUR$ is constant
  
  (NOT (DA-XVARIABLE.IS COLOUR)))


(DEFUN DA-COLOUR.OCCURS.IN.GTERM (COLOUR GTERM &optional SOLUTION)
  
  ;;; Input:   A colour and a gterm
  ;;; Value:   a list of tafs, which denote the occurrences of gterms in \verb$GTERM$
  ;;;          which are coloured by \verb$COLOUR$.
  
  (LET ((COUNTER 0) RESULT)
       (COND ((uni-colour.are.equal COLOUR (DA-GTERM.COLOUR GTERM SOLUTION)) (LIST NIL))
	     (T (MAPCAN #'(LAMBDA (SUB.TERM)
				  (INCF COUNTER)
				  (COND ((SETQ RESULT (DA-COLOUR.OCCURS.IN.GTERM COLOUR SUB.TERM SOLUTION))
					 (MAPL #'(LAMBDA (TAFS) (SETF (CAR TAFS) (NCONC1 (CAR TAFS) COUNTER))) RESULT)
					 RESULT)))
			(DA-GTERM.TERMLIST GTERM))))))

;;;;;
;;;;;========================================================================================================
;;;;; Chapter 
;;;;; -------
;;;;;
;;;;; Functions to handle well-founded ordering.
;;;;;
;;;;;========================================================================================================


(DEFUN DA-WFO.CREATE (PARAMETERS TREE &OPTIONAL ATTRIBUTES CHANGEABLES CASE.PARAMETERS)
  
  ;;; Input:   a list of terms, a wfo-tree and an sexpression
  ;;; Effect:  creates a new wfo and stores it in the database
  ;;; Value:   the created object
  
  (LET ((WFO (MAKE-WFO :PARAMETERS PARAMETERS :TREE TREE :ATTRIBUTES ATTRIBUTES
		       :CHANGEABLES CHANGEABLES :CASE.PARAMETERS CASE.PARAMETERS)))
       WFO))


(DEFUN DA-WFO.SUGGESTED.CREATE (POSITIONS CASE.POSITIONS WFO &OPTIONAL ATTRIBUTES)
  
  ;;; Input:   a list of argument-positions, a WFO and an sexpression
  ;;; Effect:  creates a new WFO.SUGGESTED object with appropriate slot-entries.
  ;;; Value:   the created object.
  
  (MAKE-WFO.SUGGESTED :POSITIONS POSITIONS :CASE.POSITIONS CASE.POSITIONS :WFO WFO :ATTRIBUTES ATTRIBUTES))


(DEFUN DA-WFO.TREE.PRED.SET.CREATE (PRED.SET &optional instantiations)
  
  ;;; Input:  a list of termlists and a list of substitutions denoting instantiations of variables.
  ;;; Effect: creates a leaf-node of a wfo-tree with \verb$PRED.SET$ as set of predecessors
  ;;; Value:  the generated leaf
  
  (CONS 'PRED.SET (LIST PRED.SET INSTANTIATIONS)))


(DEFUN DA-WFO.TREE.CREATE (LIST.OF.CONDS.TREES &OPTIONAL ONLY.CASE.ANALYSIS)
  
  ;;; Input:  a set of dotted pairs (condition . wfo-tree)
  ;;; Value:  a new tree with \verb$LIST.OF.CONDS.TREES$ as subnodes.
  
  (CONS (COND (ONLY.CASE.ANALYSIS 'CASE.TREE)
	      (T 'TREE))
	LIST.OF.CONDS.TREES))


(DEFMACRO DA-WFO.TREE.IS.LEAF (TREE)
  
  ;;; Input:  a wfo-tree
  ;;; Value:  T iff \verb$TREE$ is a leaf-node
  
  `(EQ (CAR ,TREE) 'PRED.SET))


(DEFUN DA-WFO.TREE.IS.ESSENTIAL (TREE)

  ;;; Input:  a wfo-tree
  ;;; Value:  T iff \verb$TREE$ is a case-analysis needed by
  ;;;         the well-founded ordering 

  (EQ (CAR TREE) 'TREE))


(DEFUN DA-WFO.TREE.SUBNODES (TREE)
  
  ;;; Input:  a wfo-tree
  ;;; Value:  a list of all pairs (condition.successor-node) if \verb$TREE$ is no leaf-node.
  
  (COND ((MEMBER (CAR TREE) '(CASE.TREE TREE)) (CDR TREE))))


(DEFUN DA-WFO.TREE.PRED.SET (TREE)
  
  ;;; Input:  a wfo-tree
  ;;; Value:  the set predecessor-lists if \verb$TREE$ is a leaf.
  
  (COND ((EQ (CAR TREE) 'PRED.SET) (Second TREE))))


(defun da-wfo.tree.pred.set.instantiations (tree)

  ;;; Input:  a wfo-tree
  ;;; Value:  a list of termsubstitutions, denoting instantiations of variables.
  
  (COND ((EQ (CAR TREE) 'PRED.SET) (THIRD TREE))))


(DEFUN DA-WFO.PRED.ARE.EQUAL (PRED1 PRED2)

  ;;; Input:  two predecessor sets of some wfos.
  ;;; Effect: see value:
  ;;; Value:  T,  iff both sets denote the same predecessors.

  (AND (EQL (LENGTH PRED1) (LENGTH PRED2))
       (EVERY #'(LAMBDA (TERM1 TERM2)
		  (UNI-TERM.ARE.EQUAL TERM1 TERM2))
	      PRED1 PRED2)))


(DEFUN DA-WFO.CREATE.STRUCTURAL (VARIABLE REC.POS)

  ;;; Input:  a variable and a argument-position
  ;;; Effect: creates a suggestion to a structural wfo for the specified variable and argument-position
  ;;; Value:  the suggestion
  
  (DA-WFO.SUGGESTED.CREATE (LIST REC.POS) NIL
			   (DA-WFO.CREATE (LIST VARIABLE)
					  (DA-WFO.STRUCTURAL.TREE.CREATE VARIABLE)
					  NIL
					  (LIST VARIABLE))))


(DEFUN DA-WFO.STRUCTURAL.TREE.CREATE (VARIABLE)
  
  ;;; edited : 23.03.93 by CS
  ;;; input  : a variable
  ;;; value  : a tree denoting a structural case analysis of the parameter, the leafs are
  ;;;          term substitutions for the predecessors

  (LET ((STRUCTURE.TERMS (REVERSE (DA-SORT.CREATE.ALL.STRUCTURE.TERMS VARIABLE NIL))))
    (DA-WFO.TREE.CREATE (MAPCAR #'(LAMBDA (TERM)
				    (DA=WFO.PATH.CREATE VARIABLE TERM))
				STRUCTURE.TERMS))))


(DEFUN DA=WFO.PATH.CREATE (PARAMETER TERM)
  
  ;;; edited : 23.03.93 by CS
  ;;; input  : two terms, the first is a variable, the second is a structure term
  ;;; value  : a dotted pair denoting a path through the structural tree together with
  ;;;          the hypotheses substitutions for the structural order as leaf

  (LET ((CONSTRUCTOR.OR.INDEX (DA-TERM.SYMBOL TERM)))
    (CONS (DA-WFO.TREE.PRED.SET.CREATE 
	   (MAPCAN #'(LAMBDA (SELECTOR)
		       (COND ((DA-FUNCTION.IS.REFLEXIVE SELECTOR)
			      (LIST (UNI-TERMSUBST.CREATE.PARALLEL
				     (LIST (DA-TERM.COPY PARAMETER))
				     (LIST (DA-TERM.CREATE SELECTOR (LIST (DA-TERM.COPY PARAMETER)))))))))
		   (COND ((DA-FUNCTION.IS.CONSTRUCTOR CONSTRUCTOR.OR.INDEX)
			  (DA-SORT.SELECTORS.OF.CONSTRUCTOR CONSTRUCTOR.OR.INDEX)))))
	  (LIST (DA-LITERAL.CREATE (DA-SIGN.MINUS)
				   (DP-PREDICATE.EQUALITY)
				   (LIST (DA-TERM.COPY PARAMETER) (DA-TERM.COPY TERM))
				   (LIST 'KIND (LIST 'MATCH))
				   NIL)))))


;;;;;========================================================================================================
;;;;; Chapter 
;;;;; -------
;;;;;
;;;;; Functions to handle gterms
;;;;;========================================================================================================


(DEFMACRO DA-GTERM.CREATE (SYMBOL &OPTIONAL TERMLIST COLOURS ATTRIBUTES PNAME)
  
  ;;; Input:   a symbol, a list of terms (if symbol is a function), a colour and a list of attributes
  ;;; Value:   creates the denoted term.
  
  `(MAKE-GTERM :SYMBOL ,SYMBOL :TERMLIST ,TERMLIST :COLOURS ,COLOURS
	       :ATTRIBUTES ,ATTRIBUTES
	       :PNAME ,PNAME))


(DEFUN DA=GTERM.PRINT (GTERM STREAM DEPTH)

  ;;; Input:   a gterm, a stream and a number
  ;;; Effect:  prints \verb$GTERM$ on the denoted \verb$STREAM$ until the gterm-depth do not
  ;;;          exceed \verb$DEPTH$.
  ;;; Value:   undefined
  
  (COND ((AND *PRINT-LEVEL* (> DEPTH *PRINT-LEVEL*)) (FORMAT STREAM "#"))
	(T (FORMAT STREAM "(~A ~{ ~A~})" (DA-GTERM.SYMBOL GTERM) (DA-GTERM.TERMLIST GTERM)))))


(DEFMACRO DA-GTERM.IS (OBJECT)
  
  ;;; Input:  an object
  ;;; Value:  T, iff \verb$OBJECT$ is a term
  
  `(TYPEP ,OBJECT 'GTERM))


(DEFUN DA-GTERM.DEFINING.INPUT (GTERM)

  ;;; Input:  a gterm
  ;;; Value:  T iff this gterm is part of the actual activated database
  
  (AND GTERM (GETF (DA-GTERM.ATTRIBUTES GTERM) 'DEFINING.INPUT)))


(DEFUN DA-GTERM.IS.TRUE (LITERAL)
  
  ;;; edited at 30-JUL-85 16:28:55
  ;;; Input:  a gterm
  ;;; Value:  Returns T, if \verb$GTERM$ is equal to TRUE.
  
  (AND (DA-LITERAL.IS LITERAL)
       (DA-LITERAL.IS.POSITIVE LITERAL)
       (DA-PREDICATE.IS.TRUE (DA-GTERM.SYMBOL LITERAL))))


(DEFUN DA-GTERM.IS.FALSE (LITERAL)
  
  ;;; edited at 30-JUL-85 16:30:19
  ;;; Input:  a gterm 
  ;;; Value:  Returns T, if \verb$GTERM$ is equal to FALSE.
  
  (AND (DA-LITERAL.IS LITERAL)
       (DA-LITERAL.IS.POSITIVE LITERAL)
       (DA-PREDICATE.IS.FALSE (DA-GTERM.SYMBOL LITERAL))))


(DEFMACRO DA-GTERM.COLOUR (GTERM SOLUTION)
  
  ;;; Input:  a gterm and an indicator
  ;;; Value:  returns the colour of \verb$GTERM$ (determined by \verb$SOLUTION$)
  
  `(GETF (DA-GTERM.COLOURS ,GTERM) ,SOLUTION))


(DEFUN DA-GTERM.COPY.AND.CREATE (GTERM &KEY (SYMBOL 'UNDEF) (TERMLIST 'UNDEF) (COLOURS 'UNDEF)
				       (ATTRIBUTES 'UNDEF) (SIGN 'UNDEF))

  ;;; Input:  a gterm, and optional a function or predicate symbol, a list of gterms, a property-list
  ;;;         denoting the colours, a property-list denoting attributes and a sign.
  ;;; Effect: copys \verb$GTERM$ exept whose parts which are explicitly specified by some key
  ;;;         parameter.
  ;;; Value:  the copy of gterm.
  
  (COND ((EQ SYMBOL 'UNDEF) (SETQ SYMBOL (DA-GTERM.SYMBOL GTERM))))
  (COND ((EQ TERMLIST 'UNDEF) (SETQ TERMLIST (MAPCAR #'DA-TERM.COPY (DA-GTERM.TERMLIST GTERM)))))
  (COND ((EQ COLOURS 'UNDEF) (SETQ COLOURS (COPY-LIST (DA-GTERM.COLOURS GTERM)))))
  (COND ((EQ ATTRIBUTES 'UNDEF) (SETQ ATTRIBUTES (COPY-TREE (DA-GTERM.ATTRIBUTES GTERM)))))
  (COND ((AND (DA-LITERAL.IS GTERM) (EQ SIGN 'UNDEF) (SETQ SIGN (DA-LITERAL.SIGN GTERM)))))
  (CASE (TYPE-OF GTERM)
	(TERM (DA-TERM.CREATE SYMBOL TERMLIST COLOURS ATTRIBUTES))
	(LITERAL (DA-LITERAL.CREATE SIGN SYMBOL TERMLIST ATTRIBUTES COLOURS))
	(FORMULA (DA-FORMULA.CREATE SYMBOL TERMLIST COLOURS))
	(OTHERWISE (DA-GTERM.CREATE SYMBOL TERMLIST COLOURS ATTRIBUTES))))


(DEFUN DA-GTERM.COPY (GTERM &OPTIONAL REPLACE.COLOUR COLOUR COL.KEY)
  
  ;;; Input:  a gterm, a flag, and a colour
  ;;; Value:  a copy of \verb$GTERM$, while the attributes are not copied.
  ;;;         If the flag is t, \verb$COLOUR$ is used as colour of the copy otherwise
  ;;;         the colour-information is copied from \verb$GTERM$.
  
  (CASE (TYPE-OF GTERM)
	(TERM (DA-TERM.COPY GTERM REPLACE.COLOUR COLOUR COL.KEY))
	(LITERAL (DA-LITERAL.COPY GTERM REPLACE.COLOUR COLOUR COL.KEY))
	(FORMULA (DA-FORMULA.COPY GTERM REPLACE.COLOUR COLOUR COL.KEY))
	(OTHERWISE (LET ((ATTR (COPY-TREE (DA-GTERM.ATTRIBUTES GTERM))))
		     (COND ((GETF ATTR 'ACTIVE)
			    (SETF (GETF ATTR 'ACTIVE) NIL)))
		     (MAKE-GTERM :SYMBOL (DA-GTERM.SYMBOL GTERM)
				 :TERMLIST (MAPCAR #'(LAMBDA (STERM)
						       (DA-GTERM.COPY STERM REPLACE.COLOUR COLOUR COL.KEY))
						   (DA-GTERM.TERMLIST GTERM))
				 :COLOURS (COND (REPLACE.COLOUR (OR COLOUR (LIST COL.KEY (DA-COLOUR.CREATE.VARIABLE))))
						(T (COPY-LIST (DA-GTERM.COLOURS GTERM))))
				 :ATTRIBUTES ATTR)))))


(DEFUN DA-GTERM.DEPTH (GTERM)
  
  ;;; INPUT:  A gterm                    
  ;;; VALUE:  the maximal depth of the \verb$GTERM$.
  
  (COND ((NULL (DA-GTERM.TERMLIST GTERM)) 0)
	(T (LET ((MAX.DEPTH 0))
		(MAPC #'(LAMBDA (SUBTERM)
				(SETQ MAX.DEPTH (MAX MAX.DEPTH (DA-GTERM.DEPTH SUBTERM))))
		      (DA-GTERM.TERMLIST GTERM))
		(1+ MAX.DEPTH)))))


(DEFUN DA-GTERM.SIZE (GTERM)
  
  ;;; Input:  a gterm
  ;;; Value:  the number of functions predicates and junctions of \verb$GTERM$
  
  (LET ((SIZE 1))
    (MAPC #'(LAMBDA (SUB.TERM)
	      (INCF SIZE (DA-GTERM.SIZE SUB.TERM)))
	  (DA-GTERM.TERMLIST GTERM))
    SIZE))



(DEFUN DA-GTERM.GREATER (GTERM1 GTERM2)
  
  ;;; Input:  two terms
  ;;; Value:  T, iff \verb$GTERM1$ is less than \verb$GTERM2$ according to the size of both
  
   (LET ((V1 (DA-GTERM.VARIABLES GTERM1)) (V2 (DA-GTERM.VARIABLES GTERM2))
	(C1 (DA-GTERM.CONSTANTS GTERM1 'SKOLEM)) (C2 (DA-GTERM.CONSTANTS GTERM2 'SKOLEM))
	S1 S2)
    (SETQ S1 (+ (LENGTH V1) (LENGTH C1)))
    (SETQ S2 (+ (LENGTH V2) (LENGTH C2)))
    (COND ((> S1 S2))
	  ((EQL S1 S2)
	   (SETQ S1 (- (LENGTH C1) (LENGTH V1)))
	   (SETQ S2(- (LENGTH C2) (LENGTH V2)))
	   (COND ((> S1 S2))
		 ((EQL S1 S2)
		  (SETQ S1 (DA-GTERM.SIZE GTERM1))
		  (SETQ S2 (DA-GTERM.SIZE GTERM2))
		  (> S1 S2)))))))

			; (EQL S1 S2)
			;  (DA-GTERM.LEX.GREATER GTERM1 GTERM2)



(DEFUN DA-GTERM.LEX.GREATER (GTERM1 GTERM2)

  ;;; Input:  two terms
  ;;; Value:  T, iff \verb$GTERM1$ is less than \verb$GTERM2$ according to the lexicographical
  ;;;         ordering of their printed representation.

  (LET (RESULT)
    (COND ((STRING> (DA-SYMBOL.PNAME (DA-GTERM.SYMBOL GTERM1))
		    (DA-SYMBOL.PNAME (DA-GTERM.SYMBOL GTERM2))))
	  ((AND (STRING= (DA-SYMBOL.PNAME (DA-GTERM.SYMBOL GTERM1))
			 (DA-SYMBOL.PNAME (DA-GTERM.SYMBOL GTERM2)))
		(SOME #'(LAMBDA (SUB.TERM1 SUB.TERM2)
			  (SETQ RESULT (COND ((DA-GTERM.LEX.GREATER SUB.TERM1 SUB.TERM2) 1)
				     ((DA-GTERM.LEX.GREATER SUB.TERM2 SUB.TERM1) 2))))
		    (DA-GTERM.TERMLIST GTERM1) (DA-GTERM.TERMLIST GTERM2)))
	   (EQL RESULT 1)))))


(defun da-gterm.taf.is.unnegated (gterm taf)

  ;;; Input:  a gterm and a term-access function
  ;;; Effect: tests whether \verb$TAF$ occurs unnegated inside \verb$GTERM$
  ;;; Value:  returns t iff \verb$GTERM$ satisfies the condition.

  (let ((result t) symbol)
    (mapl #'(lambda (taf)
	    (setq symbol (da-gterm.symbol (da-access (cdr taf) gterm)))
	    (cond ((or (member symbol '(not eqv))
			(and (eq symbol 'impl) (eql (car taf) 1)))
		   (setq result nil))))
	  taf)
    result))



(DEFUN DA-GTERM.COMMON.SUPERTERM (GTERM1 GTERM2 &OPTIONAL TAF)

  ;;; Input:  two gterms
  ;;; Effect: computes the deepest term-access-function such that both gterms disagree only in these parts
  ;;; Value:  a multiple value: the computed term-access-function and a flag indicating whether both gterms
  ;;;         disagree at all.

  (COND ((NEQ (DA-GTERM.SYMBOL GTERM1) (DA-GTERM.SYMBOL GTERM2))
	 (VALUES TAF T))
	(T (LET ((INNER.TAF (DA-TAF.CREATE.ZERO TAF)) FAILURE.TAF FAILURE)
	     (COND ((EVERY #'(LAMBDA (SUB.GTERM1 SUB.GTERM2)
			       (SETQ INNER.TAF (DA-TAF.CREATE.NEXT INNER.TAF))
			       (MULTIPLE-VALUE-BIND (TAF RESULT)
				 (DA-GTERM.COMMON.SUPERTERM SUB.GTERM1 SUB.GTERM2 INNER.TAF)
				 (COND ((NULL RESULT) T)
				 ((NULL FAILURE)
				  (SETQ FAILURE.TAF TAF)
				  (SETQ FAILURE RESULT)))))
			   (DA-GTERM.TERMLIST GTERM1) (DA-GTERM.TERMLIST GTERM2))
		    (VALUES FAILURE.TAF FAILURE))
		   (T (VALUES TAF T)))))))


(DEFUN DA-GTERM.FUNCTIONS.MULTISET (GTERM)
  
  ;;; Edited    : 10.03.1994
  ;;; Input :     a gterm
  ;;; Effect    : see value.
  ;;; Value     : a multiset of all function symbols of the \verb$GTERM$, including skolem constants and
  ;;;             skolem-functions.
  
  (NCONC (COND ((DA-FUNCTION.IS (DA-GTERM.SYMBOL GTERM)) (LIST (DA-GTERM.SYMBOL GTERM))))
	 (MAPCAN #'(LAMBDA (SUBGTERM) (DA-GTERM.FUNCTIONS.MULTISET SUBGTERM))
		 (DA-GTERM.TERMLIST GTERM))))


(DEFUN DA-GTERM.OCCURS.IN.TERMLIST (GTERM TERMLIST &OPTIONAL ENV1 ENV2)
  
  ;;; Input:   a gterm and a termlist
  ;;; Value:   a list of tafs, which denote the occurrences of \verb$GTERM$ in \verb$TERMLIST$.
  
  (LET ((COUNTER 0) RESULT)
       (MAPCAN #'(LAMBDA (SUB.TERM)
			 (INCF COUNTER)
			 (COND ((UNI-GTERM.ARE.EQUAL SUB.TERM GTERM ENV1 ENV2) (LIST (LIST COUNTER)))
			       ((SETQ RESULT (DA-GTERM.OCCURS.IN.TERMLIST GTERM (DA-TERM.TERMLIST SUB.TERM) ENV1 ENV2))
				(MAPL #'(LAMBDA (TAFS) (SETF (CAR TAFS) (NCONC1 (CAR TAFS) COUNTER))) RESULT)
				RESULT)))
	       TERMLIST)))


(DEFUN DA-GTERM.OCCURS.IN.GTERM (GTERM1 GTERM2 &OPTIONAL ENV1 ENV2)
  
  ;;; Input:   two gterms
  ;;; Value:   a list of tafs, which denote the occurrences of \verb$GTERM1$ in \verb$GTERM2$.
  
  (LET ((COUNTER 0) RESULT)
       (COND ((UNI-GTERM.ARE.EQUAL GTERM1 GTERM2 ENV1 ENV2) (LIST NIL))
	     (T (MAPCAN #'(LAMBDA (SUB.TERM)
				  (INCF COUNTER)
				  (COND ((SETQ RESULT (DA-GTERM.OCCURS.IN.GTERM GTERM1 SUB.TERM ENV1 ENV2))
					 (MAPL #'(LAMBDA (TAFS) (SETF (CAR TAFS) (NCONC1 (CAR TAFS) COUNTER))) RESULT)
					 RESULT)))
			(DA-GTERM.TERMLIST GTERM2))))))


(DEFUN DA-GTERM.TAFS (GTERM APPLY.FCT)

  ;;; Input:  a gterm and a lambda expression $F$ with one argument
  ;;; Value:  a list of term-access-function denoting whose subterms of
  ;;;         \verb$GTERM$ which satisfy the test $F$.

  (LET ((COUNTER 0) RESULT)
    (COND ((FUNCALL APPLY.FCT GTERM) (LIST NIL))
	  (T (MAPCAN #'(LAMBDA (SUB.TERM)
			 (INCF COUNTER)
			 (COND ((SETQ RESULT (DA-GTERM.TAFS SUB.TERM APPLY.FCT))
				(MAPL #'(LAMBDA (TAFS) (SETF (CAR TAFS) (NCONC1 (CAR TAFS) COUNTER))) RESULT)
				RESULT)))
		     (DA-GTERM.TERMLIST GTERM))))))


(DEFUN DA-GTERM.LITERAL.TAFS (GTERM APPLY.FCT)

  ;;; Input:  a gterm and a lambda expression $F$ with one argument
  ;;; Value:  a list of term-access-function denoting whose literals of
  ;;;         \verb$GTERM$ which satisfy the test $F$.

  (LET ((COUNTER 0) RESULT)
    (COND ((da-literal.is gterm) (cond ((FUNCALL APPLY.FCT GTERM) (LIST NIL))))
	  (t  (MAPCAN #'(LAMBDA (SUB.TERM)
			 (INCF COUNTER)
			 (COND ((SETQ RESULT (DA-GTERM.literal.TAFS SUB.TERM APPLY.FCT))
				(MAPL #'(LAMBDA (TAFS) (SETF (CAR TAFS) (NCONC1 (CAR TAFS) COUNTER))) RESULT)
				RESULT)))
		     (DA-GTERM.TERMLIST GTERM))))))


(DEFUN DA-GTERM.PSEUDO.CONSTANTS (GTERM)
  
  ;;; Input :  A term
  ;;; Value :  a list of all "pseudo constants" occurring in \verb$GTERM$ as defined in the function 
  ;;;          da-term.is.pseudo.constant
  
  (COND ((DA-GTERM.IS.PSEUDO.CONSTANT GTERM)
	 (LIST GTERM))
	(T (DELETE-DUPLICATES (MAPCAN #'DA-GTERM.PSEUDO.CONSTANTS (DA-GTERM.TERMLIST GTERM)) :TEST 'UNI-GTERM.ARE.EQUAL))))


(DEFUN DA-GTERM.IS.PSEUDO.CONSTANT (GTERM)
  
  ;;; Input:  a term
  ;;; Value:  T, if \verb$GTERM$ is a term build up of skolem-constants, selector- and index-functions.
  
  (LET ((SYMBOL (DA-TERM.SYMBOL GTERM)))
       (AND (DA-TERM.IS GTERM)
	    (NOT (DA-VARIABLE.IS SYMBOL))
	    (OR (AND (DA-FUNCTION.SKOLEM SYMBOL)
		     (NULL (DA-FUNCTION.DOMAIN.SORTS SYMBOL)))
		(AND (OR (DA-SYMBOL.HAS.ATTRIBUTE SYMBOL 'SEL.STRUCTURE)
			 (DA-SYMBOL.HAS.ATTRIBUTE SYMBOL 'INDEX.FCT))
		     (DA-GTERM.IS.PSEUDO.CONSTANT (CAR (DA-TERM.TERMLIST GTERM))))))))


(DEFUN DA-GTERM.ONE.SIDE.FUNCTIONS (TERM1 TERM2)
  
  ;;; input:  two terms
  ;;; Value:  a multiple value containing two lists of functionssymbols, which are those occurring only
  ;;;         in one of the given terms and there is also no funtionssymbol in the other term defined by
  ;;;         the help of these functions.
  
  (LET ((PREFUNS1 (DA-GTERM.FUNCTIONS TERM1)) (PREFUNS2 (DA-GTERM.FUNCTIONS TERM2)))
       (VALUES (DELETE-IF #'(LAMBDA (F)
			      (or (da-function.skolem f)
				  (da-function.is.selector f)
				  (da-function.is.constructor f)
				  (not (da-prefun.is.independent f PREFUNS2))
				  (not (da-prefun.is.independent f (remove f prefuns1)))))
			  (SET-DIFFERENCE PREFUNS1 PREFUNS2))
	       (DELETE-IF #'(LAMBDA (F)
			      (or (da-function.skolem f)
				  (da-function.is.selector f)
				  (da-function.is.constructor f)
				  (not (da-prefun.is.independent f PREFUNS1))
				  (not (da-prefun.is.independent f (remove f prefuns2)))))
			  (SET-DIFFERENCE PREFUNS2 PREFUNS1)))))


(DEFUN DA-GTERM.IS.FADE (GTERM &OPTIONAL SOLUTION)
  
  ;;; Input :  A gterm
  ;;; Value :  T, if each part of \verb$GTERM$ has a fade colour (indicated by \verb$SOLUTION$)
  
  (AND (DA-COLOUR.IS.FADE (DA-GTERM.COLOUR GTERM SOLUTION))
       (EVERY #'(LAMBDA (SUB.TERM) (DA-GTERM.IS.FADE SUB.TERM SOLUTION))
	      (DA-GTERM.TERMLIST GTERM))))


(DEFUN DA-GTERM.IS.COLOURED (GTERM &OPTIONAL SOLUTION)
  
  ;;; Input :  A gterm
  ;;; Value :  T, if each part of \verb$GTERM$ has a non-fade colour (indicated by \verb$SOLUTION$)
  
  (AND (NOT (DA-COLOUR.IS.FADE (DA-GTERM.COLOUR GTERM SOLUTION)))
       (EVERY #'(LAMBDA (SUB.TERM) (DA-GTERM.IS.COLOURED SUB.TERM SOLUTION))
	      (DA-GTERM.TERMLIST GTERM))))


(DEFUN DA-GTERM.COLOURIZE (GTERM &OPTIONAL COLOUR SOLUTION)
  
  ;;; Input  : a gterm
  ;;; Effect : the colour of all subterms of \verb$GTERM$ are painted either in \verb$COLOUR$ in all different
  ;;;          new (non-faded) colours.
  ;;; Value  : the colourized gterm
  
  (SETF (GETF (DA-GTERM.COLOURS GTERM) SOLUTION) (COND (COLOUR) (T (DA-COLOUR.CREATE.VARIABLE))))
  (MAPC #'(LAMBDA (SUB.TERM) (DA-GTERM.COLOURIZE SUB.TERM COLOUR SOLUTION))
	(DA-GTERM.TERMLIST GTERM))
  GTERM)


(defun da-gterm.colourize.until (gterm tafs colour solution &optional taf)

  ;;; Input  : a gterm, a list of tafs, a colour, and a colour-key
  ;;; Effect : the colour of all symbols of \verb$GTERM$ up to \verb$TAFS$ (exclusive) are painted
  ;;;          in \verb$COLOUR$.
  ;;; Value  : the colourized gterm

  (cond ((member taf tafs :test 'equal))
	(t (cond (colour (setf (da-gterm.colour gterm solution) colour))
		 (t (remf (da-gterm.colours gterm) solution)))
	   (setq taf (da-taf.create.zero taf))
	   (mapc #'(lambda (sub.gterm)
		     (setq taf (da-taf.create.next taf))
		     (da-gterm.colourize.until sub.gterm tafs colour solution taf))
		 (da-gterm.termlist gterm)))))


(defun da-gterm.colourize.context (gterm colour.key value)

  ;;; Input:  a gterm, an indicator and a colour
  ;;; Effect: colours the top-level context (indicated by \verb$COLOUR.KEY$)
  ;;;         of \verb$GTERM$ by \verb$VALUE$
  ;;; Value:  the coloured gterm.
  
  (cond ((DA-COLOUR.IS.FADE (DA-GTERM.COLOUR GTERM  colour.key))
	 (setf (getf (da-gterm.colours gterm) colour.key) value)
	 (mapc #'(lambda (sub.term)
		   (da-gterm.colourize.context sub.term colour.key value))
	       (da-gterm.termlist gterm)))))


(defun da-gterm.colour.replace (gterm colour.key colour1 colour2)

  (cond ((UNI-GTERM.are.equal (da-gterm.colour gterm colour.key) colour1)
	 (setf (getf (da-gterm.colours gterm) colour.key) colour2)))
  (mapc #'(lambda (subgterm)
	    (da-gterm.colour.replace subgterm colour.key colour1 colour2))
	(da-gterm.termlist gterm)))


(DEFUN DA-GTERM.COLOUR.REMOVE (GTERM &OPTIONAL COLOUR.KEY)
  
  ;;; Input  : a gterm and a key of the colour
  ;;; Effect : the colour of all subterms of \verb$GTERM$ are removed
  ;;; Value  : the non-coloured gterm
  
  (COND ((NULL COLOUR.KEY) (SETF (DA-GTERM.COLOURS GTERM) NIL))
	(T (REMF (DA-GTERM.COLOURS GTERM) COLOUR.KEY)))
  (MAPC #'(LAMBDA (SUB.TERM)
	    (DA-GTERM.COLOUR.REMOVE SUB.TERM COLOUR.KEY))
	(DA-GTERM.TERMLIST GTERM))
  GTERM)


(DEFUN DA-GTERM.COLOURFUL.TERMS (GTERM &OPTIONAL SOLUTION TAF)
  
  ;;; Input : a term, a term access function
  ;;; Effect: computes all tafs, which access to the next sub.term of \verb$GTERM$ with non-faded symbol
  ;;;         (indicated by \verb$SOLUTION$). 
  ;;; Value : list of these tafs
  
  (COND ((OR (NULL (DA-GTERM.COLOUR GTERM SOLUTION))
	     (DA-COLOUR.IS.FADE (DA-GTERM.COLOUR GTERM SOLUTION)))
	 (SETQ TAF (DA-TAF.CREATE.ZERO TAF))
	 (MAPCAN #'(LAMBDA (SUB.TERM) 
			   (DA-GTERM.COLOURFUL.TERMS SUB.TERM SOLUTION (SETQ TAF (DA-TAF.CREATE.NEXT TAF))))
		 (DA-GTERM.TERMLIST GTERM)))
	(T (LIST TAF))))


(DEFUN DA-GTERM.COLOURED.TERMS (GTERM COLOUR &OPTIONAL SOLUTION TAF)
  
  ;;; Input : a term, a colour and optionally an index of the colour-slot and a term access function
  ;;; Effect: computes all tafs (composed with \verb$TAF$), which access to the next sub.term of \verb$GTERM$ with colour
  ;;;         \verb$COLOUR$ (indicated by \verb$SOLUTION$).
  ;;; Value : list of these tafs 
  
  (COND ((NOT (UNI-COLOUR.ARE.EQUAL COLOUR (DA-GTERM.COLOUR GTERM SOLUTION)))
	 (SETQ TAF (DA-TAF.CREATE.ZERO TAF))
	 (MAPCAN #'(LAMBDA (SUB.TERM) 
			   (DA-GTERM.COLOURED.TERMS SUB.TERM COLOUR SOLUTION (SETQ TAF (DA-TAF.CREATE.NEXT TAF))))
		 (DA-GTERM.TERMLIST GTERM)))
	(T (LIST TAF))))


(DEFUN DA-GTERM.OR.COLOURED.TERMS (GTERM COLOURS &OPTIONAL SOLUTION TAF)
  
  ;;; Input : a term, a colour and optionally an index of the colour-slot and a term access function
  ;;; Effect: computes all tafs (composed with \verb$TAF$), which access to the next sub.term of \verb$GTERM$ with colour
  ;;;         \verb$COLOUR$ (indicated by \verb$SOLUTION$).
  ;;; Value : list of these tafs 
  
  (COND ((NOT (MEMBER (DA-GTERM.COLOUR GTERM SOLUTION) COLOURS))
	 (SETQ TAF (DA-TAF.CREATE.ZERO TAF))
	 (MAPCAN #'(LAMBDA (SUB.TERM) 
			   (DA-GTERM.OR.COLOURED.TERMS SUB.TERM COLOURS SOLUTION (SETQ TAF (DA-TAF.CREATE.NEXT TAF))))
		 (DA-GTERM.TERMLIST GTERM)))
	(T (LIST TAF))))


(DEFUN DA-GTERM.FADE.GTERMS (GTERM &OPTIONAL SOLUTION TAF)
  
  ;;; Input : a term and a term access function
  ;;; Effect: computes all tafs (composed with \verb$TAF$), which access to the next sub.term of \verb$GTERM$
  ;;;         with faded symbol (indicated by \verb$SOLUTION$).
  ;;; Value : list of these tafs
  
  (COND ((NOT (DA-COLOUR.IS.FADE (DA-GTERM.COLOUR GTERM SOLUTION)))
	 (SETQ TAF (DA-TAF.CREATE.ZERO TAF))
	 (MAPCAN #'(LAMBDA (SUB.GTERM) 
			   (DA-GTERM.FADE.GTERMS SUB.GTERM SOLUTION (SETQ TAF (DA-TAF.CREATE.NEXT TAF))))
		 (DA-GTERM.TERMLIST gTERM)))
	(T (LIST TAF))))


(DEFUN DA-GTERM.MAX.COLOURED.GTERMS (GTERM &OPTIONAL SOLUTION TAF PRED.IS.FADED)
  
  ;;; Input : term, a term access function
  ;;; Effect: computes all tafs (composed with \verb$TAF$), which access to the all subterms of
  ;;;         \verb$GTERM$ which are coloured and their superterm is not (indicated by \verb$SOLUTION$).
  ;;; Value : list of tafs
  
  (LET (TAFS SUB.TAF)
       (SETQ SUB.TAF (DA-TAF.CREATE.ZERO TAF))
       (SETQ TAFS (MAPCAN #'(LAMBDA (SUB.GTERM) 
				    (DA-GTERM.MAX.COLOURED.GTERMS
				     SUB.GTERM SOLUTION
				     (SETQ SUB.TAF (DA-TAF.CREATE.NEXT SUB.TAF))
				     (DA-COLOUR.IS.FADE (DA-GTERM.COLOUR GTERM SOLUTION))))
			  (DA-GTERM.TERMLIST GTERM)))
       (COND ((AND PRED.IS.FADED (NOT (DA-COLOUR.IS.FADE (DA-GTERM.COLOUR GTERM SOLUTION))))
	      (PUSH TAF TAFS)))
       TAFS))


(DEFUN DA-GTERM.MAX.FADED.GTERMS (GTERM &OPTIONAL SOLUTION TAF PRED.IS.FADED)

  ;;; Input : a (coloured) term, its colour indicator, a term access function and a flag
  ;;; Effect: computes all tafs (composed with \verb$TAF$), which access to all subterms of \verb$GTERM$
  ;;;         which are faded and their direct superterm is coloured or non-existing (indicated by \verb$SOLUTION$).
  ;;; Value : list of tafs
  
  (LET (TAFS SUB.TAF)
       (SETQ SUB.TAF (DA-TAF.CREATE.ZERO TAF))
       (SETQ TAFS (MAPCAN #'(LAMBDA (SUB) 
				    (DA-GTERM.MAX.FADED.GTERMS
				     SUB SOLUTION (SETQ SUB.TAF (DA-TAF.CREATE.NEXT SUB.TAF))
				     (DA-COLOUR.IS.FADE (DA-GTERM.COLOUR GTERM SOLUTION))))
			  (DA-GTERM.TERMLIST GTERM)))
       (COND ((AND (NOT PRED.IS.FADED)
		   (DA-COLOUR.IS.FADE (DA-GTERM.COLOUR GTERM SOLUTION)))
	      (PUSH TAF TAFS)))
       TAFS))



(DEFUN DA-GTERM.SOME.SKELETON (GTERM SOLUTION)

  ;;; Input:   a (coloured) gterm and its colour indicator
  ;;; Effect:  see value:
  ;;; Value:   a member of the skeleton of \verb$GERM$.

  (COND ((DA-COLOUR.IS.FADE (DA-GTERM.COLOUR GTERM SOLUTION))
	 (SOME #'(LAMBDA (SUB.TERM)
		   (DA-GTERM.SOME.SKELETON SUB.TERM SOLUTION))
	       (DA-GTERM.TERMLIST GTERM)))
	(T (DA-TERM.CREATE (DA-TERM.SYMBOL GTERM)
			   (MAPCAR #'(LAMBDA (SUB.TERM) (DA-GTERM.SOME.SKELETON SUB.TERM SOLUTION))
				   (DA-GTERM.TERMLIST GTERM))
			   (DA-GTERM.COLOURS GTERM)))))
					 


(DEFUN DA-GTERM.VARIABLES (EXPRESSION &OPTIONAL VARS)
  
  ;;; Input  : an expression and optional a list of variables
  ;;; Value  : the list of all variables (composed with \verb$VARS$) occurring in \verb$EXPRESSION$
  
  (COND ((DA-VARIABLE.IS (DA-GTERM.SYMBOL EXPRESSION))
	 (SETQ VARS (ADJOIN (DA-GTERM.SYMBOL EXPRESSION) VARS)))
	(T (MAPC #'(LAMBDA (GTERM)
			   (SETQ VARS (DA-GTERM.VARIABLES GTERM VARS)))
		 (DA-GTERM.TERMLIST EXPRESSION))))
  VARS)


(DEFUN DA-GTERM.VARIABLES.ALONG.TAF (GTERM TAF)

  ;;; Input:   a gterm and a term-access-function
  ;;; Effect:  computes all variables which occur in the disjunctive parts
  ;;;          of the subformula denoted by \verb$TAF$ in \verb$GTERM$.
  ;;; Value:   the set of variables.

  (LET (POINTER VARS SUB.TERM)
    (MAPL #'(LAMBDA (SUB.TAF)
	      (SETQ SUB.TERM (DA-ACCESS SUB.TAF GTERM))
	      (COND ((EQ 'OR (DA-GTERM.SYMBOL GTERM))
		     (SETQ POINTER 0)
		     (MAPC #'(LAMBDA (S.T)
			       (INCF POINTER)
			       (COND ((NEQ POINTER (CAR SUB.TAF))
				      (SETQ VARS (UNION VARS (DA-GTERM.VARIABLES S.T))))))
			   (DA-GTERM.TERMLIST SUB.TERM)))))
	  TAF)
    VARS))


(DEFUN DA-GTERM.XVARIABLES (EXPRESSION COLOUR.KEY &OPTIONAL VARS)
  
  ;;; Input  : an expression and optional a list of variables
  ;;; Value  : the list of all x-variables (composed with \verb$VARS$ and indicated by \verb$COLOUR.KEY$)
  ;;;          occurring in \verb$EXPRESSION$
  
  (COND ((DA-XVARIABLE.IS (DA-GTERM.COLOUR EXPRESSION COLOUR.KEY))
	 (SETQ VARS (ADJOIN (DA-GTERM.COLOUR EXPRESSION COLOUR.KEY) VARS)))
	(T (MAPC #'(LAMBDA (GTERM)
		     (SETQ VARS (DA-GTERM.XVARIABLES GTERM COLOUR.KEY VARS)))
		 (DA-GTERM.TERMLIST EXPRESSION))))
  VARS)


(DEFUN DA-GTERM.PREFUNS (EXPRESSION &OPTIONAL PREFUNS)

  ;;; Input:  a sexpression (and a list of predicate or function symbols)
  ;;; Value:  a list of all predicate or function symbols occurring in \verb$EXPRESSION$
  ;;;         (or \verb$PREFUNS$).

  (LET ((SYMBOL (DA-GTERM.SYMBOL EXPRESSION)))
    (COND ((DA-PREFUN.IS (DA-GTERM.SYMBOL EXPRESSION))
	   (SETQ PREFUNS (ADJOIN SYMBOL PREFUNS))))
    (MAPC #'(LAMBDA (GTERM)
	      (SETQ PREFUNS (DA-GTERM.PREFUNS GTERM PREFUNS)))
	  (DA-GTERM.TERMLIST EXPRESSION))
    PREFUNS))


(DEFUN DA-GTERM.FUNCTIONS (EXPRESSION &OPTIONAL FLAG FCTS)
  
  ;;; Input  : an expression and optional a list of variables
  ;;; Value  : the list of all function symbols occurring in \verb$EXPRESSION$
  ;;;          (or \verb$FCTS$)
  
  (LET ((SYMBOL (DA-GTERM.SYMBOL EXPRESSION)))
       (COND ((DA-FUNCTION.IS (DA-GTERM.SYMBOL EXPRESSION))
	      (COND ((OR (NULL FLAG)
			 (AND (EQ FLAG 'SKOLEM) (DA-FUNCTION.SKOLEM SYMBOL)))	    
		     (SETQ FCTS (ADJOIN SYMBOL FCTS))))))
       (MAPC #'(LAMBDA (GTERM)
		       (SETQ FCTS (DA-GTERM.FUNCTIONS GTERM FLAG FCTS)))
	     (DA-GTERM.TERMLIST EXPRESSION))
       FCTS))


(DEFUN DA-GTERM.CONSTANTS (expression FLAG &OPTIONAL CONSTS)
  
  ;;; Input  : a gterm,  a flag either 'skolem, 'noskolem, or 'all, denoting which kind of 
  ;;;          constants are wanted, and optional a list of constants
  ;;; Value  : a list of all constants of the kind denoted by the \verb$FLAG$ occurring in \verb$EXPRESSION$,
  ;;;          appendend to the given list \verb$CONSTS$
  
  (LET ((SYMBOL (DA-GTERM.SYMBOL EXPRESSION)))
       (COND ((AND (DA-FUNCTION.IS SYMBOL)
		   (NULL (DA-FUNCTION.DOMAIN.SORTS SYMBOL)))
	      (COND ((OR (EQ FLAG 'ALL)
			 (AND (EQ FLAG 'SKOLEM) (DA-FUNCTION.SKOLEM SYMBOL))
			 (AND (EQ FLAG 'NOSKOLEM) (NOT (DA-FUNCTION.SKOLEM SYMBOL))))
		     (SETQ CONSTS (ADJOIN SYMBOL CONSTS)))))
	     (T (MAPC #'(LAMBDA (GTERM)
				(SETQ CONSTS (DA-GTERM.CONSTANTS GTERM FLAG CONSTS)))
		      (DA-GTERM.TERMLIST EXPRESSION))))
       CONSTS))


(DEFUN DA-GTERM.PREDICATES (EXPRESSION &OPTIONAL PREDS)
  
  ;;; Input  : an expression and optional a list of variables
  ;;; Value  : the list of all function symbols occurring in the expression and in PREDS
  
  (COND ((DA-PREDICATE.IS (DA-GTERM.SYMBOL EXPRESSION))
	 (SETQ PREDS (ADJOIN (DA-GTERM.SYMBOL EXPRESSION) PREDS))))
  (COND ((NOT (DA-TERM.IS EXPRESSION))
	 (MAPC #'(LAMBDA (GTERM)
			 (SETQ PREDS (DA-GTERM.PREDICATES GTERM PREDS)))
	       (DA-GTERM.TERMLIST EXPRESSION))))
  PREDS)


(DEFUN DA-GTERM.REMOVED.VARIABLES (GTERM1 GTERM2)

  ;;; Input  : two gterms which have the same top level symbol
  ;;; Value:  a list of pairs containing argument-position of the subterms and the removed
  ;;;         symbols for this position.
  ;;;         Example: given the gterms $f(x,g(h(y),z))$ and $(f(h(y)), g(z,x))$ the functions
  ;;;         returns the list $( ((1) (x))  ((2) (y)) )$.

  (LET ((TAF (DA-TAF.CREATE.ZERO NIL)))
    (COND ((EQ (DA-GTERM.SYMBOL GTERM1) (DA-GTERM.SYMBOL GTERM2))
	   (MAPCAR #'(LAMBDA (S.GTERM1 S.GTERM2)
		       (SETQ TAF (DA-TAF.CREATE.NEXT TAF))
		       (LIST TAF (SET-DIFFERENCE (DA-GTERM.VARIABLES S.GTERM1) (DA-GTERM.VARIABLES S.GTERM2))))
		   (DA-GTERM.TERMLIST GTERM1) (DA-GTERM.TERMLIST GTERM2))))))


(DEFUN DA-GTERM.REMOVED.SYMBOLS (GTERM1 GTERM2 VARIABLES FUNCTIONS SKOLEM.FUNCTIONS CONSTANTS SKOLEM.CONSTANTS)

  ;;; Input :  two gterms which have the same top level symbol
  ;;; Value :  a list of pairs containing argument-position of the subterms and the removed
  ;;;          symbols for this position.
  ;;;          Example: given the gterms $f(x,g(h(y),z))$ and $(f(h(y)), g(z,x))$ the functions
  ;;;          returns the list $( ((1) (x))  ((2) (y)) )$.

  (LET ((TAF (DA-TAF.CREATE.ZERO NIL)))
    (COND ((EQ (DA-GTERM.SYMBOL GTERM1) (DA-GTERM.SYMBOL GTERM2))
	   (MAPCAR #'(LAMBDA (S.GTERM1 S.GTERM2)
		       (SETQ TAF (DA-TAF.CREATE.NEXT TAF))
		       (LIST TAF (NCONC (AND VARIABLES
					     (SET-DIFFERENCE (DA-GTERM.VARIABLES S.GTERM1)
							     (DA-GTERM.VARIABLES S.GTERM2)))
					
					(COND ((AND FUNCTIONS
						    SKOLEM.FUNCTIONS)
					       (SET-DIFFERENCE (DA-GTERM.FUNCTIONS S.GTERM1 'SKOLEM)
							       (DA-GTERM.FUNCTIONS S.GTERM2 'SKOLEM)))
					      (FUNCTIONS
					       (SET-DIFFERENCE (DA-GTERM.FUNCTIONS S.GTERM1)
							       (DA-GTERM.FUNCTIONS S.GTERM2)))
					      (SKOLEM.FUNCTIONS
					       (MAPCAN #'(LAMBDA (PREFUN)
							   (AND (DA-FUNCTION.SKOLEM PREFUN)
								(LIST PREFUN)))
						       (SET-DIFFERENCE (DA-GTERM.FUNCTIONS S.GTERM1 'SKOLEM)
								       (DA-GTERM.FUNCTIONS S.GTERM2 'SKOLEM)))))
					
					(COND ((AND CONSTANTS
						    SKOLEM.CONSTANTS)
					       (SET-DIFFERENCE (DA-GTERM.CONSTANTS S.GTERM1 'ALL)
							       (DA-GTERM.CONSTANTS S.GTERM2 'ALL)))
					      (CONSTANTS
					       (SET-DIFFERENCE (DA-GTERM.CONSTANTS S.GTERM1 'NOSKOLEM)
							       (DA-GTERM.CONSTANTS S.GTERM2 'NOSKOLEM)))
					      (SKOLEM.CONSTANTS
					       (SET-DIFFERENCE (DA-GTERM.CONSTANTS S.GTERM1 'SKOLEM)
							       (DA-GTERM.CONSTANTS S.GTERM2 'SKOLEM)))))))
		   (DA-GTERM.TERMLIST GTERM1) (DA-GTERM.TERMLIST GTERM2))))))


(DEFUN DA-GTERM.PREDICATES.MULTISET (GTERM)
  
  ;;; Input:  a gterm
  ;;; Value:  a multiset of all predicate symbols of \verb$GTERM$.

  (NCONC (COND ((DA-PREDICATE.IS (DA-GTERM.SYMBOL GTERM)) (LIST (DA-GTERM.SYMBOL GTERM))))
	 (MAPCAN #'(LAMBDA (SUBGTERM) (DA-GTERM.PREDICATES.MULTISET SUBGTERM))
		 (DA-GTERM.TERMLIST GTERM))))


(DEFUN DA-GTERM.VARIABLES.MULTISET (GTERM)
  
  ;;; Input:  a gterm
  ;;; Value:  a multiset of all variables of \verb$GTERM$.

  (COND ((DA-VARIABLE.IS (DA-GTERM.SYMBOL GTERM))
	 (LIST (DA-GTERM.SYMBOL GTERM)))
	(T (MAPCAN #'(LAMBDA (SUBGTERM) (DA-GTERM.VARIABLES.MULTISET SUBGTERM)) (DA-GTERM.TERMLIST GTERM)))))


(DEFUN da-gterm.insert.taf.attributes (GTERM &OPTIONAL (TAF NIL) (TOP.GTERM GTERM))
  ;;; Input:  a gterm, a taf and a toplevel gterm
  ;;; Effect: inserts attributes 

  (COND ((DA-LITERAL.IS GTERM)
	 (SETF (GETF (DA-LITERAL.ATTRIBUTES GTERM) 'TOP.LEVEL.GTERM) (COND (TOP.GTERM) (T GTERM)))
	 (SETF (GETF (DA-LITERAL.ATTRIBUTES GTERM) 'TAF) TAF))
	((DA-TERM.IS GTERM))
	(T (SETQ TAF (DA-TAF.CREATE.ZERO TAF))
	   (MAPC #'(LAMBDA (SUB.GTERM)
		     (SETQ TAF (DA-TAF.CREATE.NEXT TAF))
		     (da-gterm.insert.taf.attributes SUB.GTERM TAF TOP.GTERM))
		 (DA-GTERM.TERMLIST GTERM)))))


(DEFUN DA-GTERM.DEFINING.SYMBOLS (GTERM)

  ;;; Input:   a gterm
  ;;; Effect:  see value
  ;;; Value:   a list of all predicate and function-symbols with the help of which
  ;;;          the symbols of \verb$GTERM$ are defined.

  (DELETE-DUPLICATES (NCONC (DELETE-IF #'(LAMBDA (FUNC)
					   (OR (DA-FUNCTION.IS.CONSTRUCTOR FUNC) (DA-FUNCTION.IS.SELECTOR FUNC)))
				       (DA-GTERM.FUNCTIONS GTERM))
			    (DELETE-IF #'(LAMBDA (PRED)
					   (DA-PREDICATE.IS.EQUALITY PRED))
				       (DA-GTERM.PREDICATES GTERM)))))


(DEFUN DA-GTERM.LITERALS.WITH.PROPERTY (GTERM APPLY.FCT &OPTIONAL TAF)
  
  ;;; Input:  a term, a lisp function(al) and a term-access-function
  ;;; Effect: walks through \verb$GTERM$ and applies \verb$APPLY.FCT$ to all literals in term.
  ;;; Value:  a list of term-access-function (concatenated with \verb$TAF$)
  ;;;         to all literals which returns a non-nil result iff \verb$APPLY.FCT$ is applied to them.
  
  (COND ((DA-LITERAL.IS GTERM)
	 (COND ((FUNCALL APPLY.FCT GTERM) (LIST TAF))))
	((DA-TERM.IS GTERM) NIL)
	(T (SETQ TAF (DA-TAF.CREATE.ZERO TAF))
	   (MAPCAN #'(LAMBDA (SUB.TERM)
			     (DA-GTERM.LITERALS.WITH.PROPERTY SUB.TERM APPLY.FCT (SETQ TAF (DA-TAF.CREATE.NEXT TAF))))
		   (DA-GTERM.TERMLIST GTERM)))))


(DEFUN DA-GTERM.MAP.LITERALS (GTERM APPLY.FCT)
  
  ;;; Input:  a term, a lisp function(al) and a term-access-function
  ;;; Effect: walks through term and applies \verb$APPLY.FCT$ to all literals in \verb$GTERM$.
  ;;; Value:  a list of term-access-function to all literals which returns a non-nil result
  ;;;         if applied to literal.
  
  (COND ((DA-LITERAL.IS GTERM)
	 (FUNCALL APPLY.FCT GTERM))
	((DA-TERM.IS GTERM) NIL)
	(T (MAPC #'(LAMBDA (SUB.TERM)
		     (DA-GTERM.MAP.LITERALS SUB.TERM APPLY.FCT))
		 (DA-GTERM.TERMLIST GTERM)))))


(DEFUN DA-GTERM.WITHOUT.TAFS (GTERM &REST TAFS)

  ;;; Input:  a gterm and a list of term-access functions
  ;;; Effect: computes a gterm where all literals of \verb$GTERM$ accessed by some taf of \verb$TAFS$ are assumed as false
  ;;; Value:  the reduced gterm
  
  (DA=GTERM.WITHOUT.TAFS GTERM (MAPCAR #'REVERSE TAFS)))


(DEFUN DA=GTERM.WITHOUT.TAFS (GTERM R.TAFS)

  ;;; Input:  a gterm and a term-access-function
  ;;; Value:  returns a gterm without the sub-gterm specified by \verb$TAF$, also every alternate AND-path is
  ;;;         removed.

  (LET (LIST (POS 0) ARGS)
    (COND ((EQ R.TAFS NIL) GTERM)
	  ((EQ (CAR R.TAFS) NIL) (da-literal.false))
	  (T (SETQ ARGS (MAPCAN #'(LAMBDA (SUBTERM)
				    (INCF POS)
				    (COND ((SETQ LIST (MAPCAN #'(LAMBDA (R.TAF)
								  (COND ((EQ (CAR R.TAF) POS)
									 (LIST (CDR R.TAF)))))
							      R.TAFS))
					   (LIST (DA=GTERM.WITHOUT.TAFS SUBTERM LIST)))
					  ((EQ 'OR (DA-GTERM.SYMBOL GTERM)) (LIST SUBTERM))))
				(DA-GTERM.TERMLIST GTERM)))
	     (COND ((EQ 'AND (DA-GTERM.SYMBOL GTERM))
		    (COND ((SOME #'(LAMBDA (ARG) (DA-FORMULA.IS.FALSE ARG)) ARGS) (DA-LITERAL.FALSE))
			  (T (DA-FORMULA.JUNCTION.CLOSURE 'AND ARGS))))
		   (T (DA-FORMULA.JUNCTION.CLOSURE 'OR (DELETE-IF #'(LAMBDA (ARG) (DA-FORMULA.IS.FALSE ARG)) ARGS))))))))


(DEFUN DA-GTERM.LIT.TAF (GTERM TAF)
  
  ;;; Input: a gterm and a taf
  ;;; Value: a subtaf of \verb$TAF$ denoting the literal of \verb$GTERM$ \verb$TAF$ is pointing to

  (WHILE (AND TAF (NOT (DA-LITERAL.IS (DA-ACCESS TAF GTERM))))
    (SETQ TAF (CDR TAF)))
  TAF)


(DEFUN DA=GTERM.CONTEXT.IS.LESS (GTERM COLOUR.KEY SYMBOL)

  (COND ((DA-COLOUR.IS.FADE (DA-GTERM.COLOUR GTERM COLOUR.KEY))
	 (OR (NOT (DA-PREFUN.IS (DA-GTERM.SYMBOL GTERM)))
	     (AND (DA-PREFUN.IS.LESS (DA-GTERM.SYMBOL GTERM) SYMBOL)
		  (EVERY #'(LAMBDA (TERM)
			     (DA=GTERM.CONTEXT.IS.LESS TERM COLOUR.KEY SYMBOL))
			 (DA-GTERM.TERMLIST GTERM)))))
	(T T)))


(defun da-gterm.compute.match.binding (gterm taf)

  ;;; Input:   a gterm and a term-access function or 'NONE
  ;;; Effect:  searches for all match literals on the paths through the subformula
  ;;;          denoted by \verb$TAF$ and uses this structural information in order
  ;;;          to compute a substitution for \verb$VARS$. Also elimination
  ;;;          equations are used to simplify the substitution
  ;;; Value:   the computed substitution.

  (let ((lits (da-formula.junction.open 'or (cond ((eq taf 'NONE) gterm)
						  (t (da-gterm.without.tafs gterm taf)))))
	termsubst match.lits other.lits selector.terms term)
    (mapc #'(lambda (lit) 
	      (cond ((and (da-literal.is lit)
			  (setq term (da-literal.is.normalized.match lit (da-sign.minus))))
		     (setq match.lits (da=gterm.insert.match.into.list match.lits term lit)))
		    ((da-literal.is.negated.equation lit)
		     (push lit other.lits))))
	  lits)
    (mapc #'(lambda (match.lit)
	      (setq termsubst (uni-termsubst.create termsubst (car match.lit) (second (da-literal.termlist (second match.lit))))))
	  match.lits)
    (smapc #'(lambda (term) (setq selector.terms (nconc selector.terms (da=gterm.selector.terms term))))
	   #'cddr
	   (cdr termsubst))
    (mapc #'(lambda (selector.term)
	      (setq termsubst (uni-termsubst.create 
			       termsubst selector.term (da-term.create (da-variable.create (da-term.sort selector.term))))))
	  (remove-duplicates selector.terms :test 'uni-gterm.are.equal))
    (setq termsubst (da=gterm.incorporate.other.equalities termsubst other.lits))
    termsubst))


(defun da=gterm.selector.terms (gterm)
  
  (cond ((and (da-function.is (da-gterm.symbol gterm))
	      (da-function.is.selector (da-gterm.symbol gterm)))
	 (list gterm))
	(t (mapcan #'(lambda (subterm) (da=gterm.selector.terms subterm))
		   (da-gterm.termlist gterm)))))


(defun da=gterm.incorporate.other.equalities (termsubst other.lits)

  (let (new.term other.term)
    (mapc #'(lambda (other.lit)
	      (setq new.term (uni-termsubst.apply termsubst (car (da-literal.termlist other.lit))))
	      (cond ((da-variable.is (da-gterm.symbol new.term))
		     (setq other.term (uni-termsubst.apply termsubst (second (da-literal.termlist other.lit))))
		     (cond ((not (da-gterm.occurs.in.gterm new.term other.term))
			    (setq termsubst (uni-termsubst.create termsubst new.term other.term)))))))
	  other.lits)
    termsubst))


(defun da=gterm.insert.match.into.list (match.list term lit)
  
  ;;; Input:   a list of tupels denoting match literals, a term, and a match literal
  ;;; Effect:  inserts the match literal denoted by \verb$TERM$ and \verb$LIT$
  ;;;          into \verb$MATCH.LIST$ such that they are ordered accprding the subterm-property.

  (cond ((null match.list) (list (list term lit)))
	((da-gterm.occurs.in.gterm (car (car match.list)) term)           ; (p(x), s, p(x) = s(p(p((x)))) vs. ((x, s,..)..)
	 (setf (cdr match.list) (da=gterm.insert.match.into.list (cdr match.list) term lit))
	 match.list)
	((da-gterm.occurs.in.gterm term (car (car match.list)))           ; (x, s, x = s(p(x))) vs. ((p(x), s, ...)...)
	 (cons (list term lit) match.list))
	(t (setf (cdr match.list) (da=gterm.insert.match.into.list (cdr match.list) term lit))
	   match.list)))


;;;;;===============================================================================================================
;;;;;
;;;;; Datastructure for algorithmic descriptions of functions and predicate definitions
;;;;; ---------------------------------------------------------------------------------
;;;;;
;;;;; Used attributes:
;;;;;
;;;;;   UNSPEC.CASES  : attribute of a definition, denoting all (missing) cases of the top-level case-analysis
;;;;;                   which are not specified by the user.
;;;;;                   The disjunction of all conditions of single cases in gterm's termlist combined with the value
;;;;;                   of this attribute is true.
;;;;;
;;;;;================================================================================================================


(DEFUN DA-GTERM.IS.DEFINITION (GTERM)
  
  ;;; Input:   a gterm 
  ;;; value:   t if \verb$GTERM$ is part of a definition.
  
  (GETF (DA-GTERM.ATTRIBUTES GTERM) 'DEFINITION))


(DEFMACRO DA-GTERM.DEF.VALUE (GTERM)

  ;;; Input:   a gterm, denoting a definition case
  ;;; Value:   the value of the definition case \verb$GTERM$
  
  `(CAR (DA-GTERM.TERMLIST ,GTERM)))


(DEFMACRO DA-GTERM.DEF.CONDITION (GTERM)

  ;;; Input:   a gterm, denoting a definition case
  ;;; Value:   the condition of the definition case \verb$GTERM$
  
  `(CDR (DA-GTERM.TERMLIST ,GTERM)))


(DEFMACRO DA-GTERM.DEF.IS.VALUE (DEFINITION)

  ;;; Input:   a gterm
  ;;; Value:   T, iff \verb$GTERM$ is a definition case

  `(getf (DA-GTERM.ATTRIBUTES ,DEFINITION) 'VALUE.OF.DEFINITION))


(DEFUN DA-GTERM.DEF.VALUE.CREATE (GTERM)

  ;;; Input:   a gterm
  ;;; Effect:  creates a value-slot of a definition case from \verb$GTERM$
  ;;; Value:   the created value-slot

  (SETF (getf (DA-GTERM.ATTRIBUTES GTERM) 'VALUE.OF.DEFINITION) t)
  GTERM)


(DEFMACRO DA-GTERM.DEF.CREATE (VALUE LITLIST)

  ;;; Input:   a value-slot and a condition of a definition case
  ;;; Effect:  creates a definition case
  ;;; Value:   the new definition case
  
  `(DA-GTERM.CREATE 'OR (CONS ,VALUE ,LITLIST)))


(DEFMACRO DA-GTERM.DEFINITION.CREATE (CASES)

  ;;; Input:   a list of definition cases
  ;;; Value:   a definition, containing all these cases
  
  `(DA-GTERM.CREATE 'AND ,CASES))


(DEFUN DA-GTERM.DEF.HOLDS.TERMINATION (DEFINITION)

  ;;; Input:   a gterm, denoting a (part of a) definition
  ;;; Value:   a list of recursion orderings which are based on the top-level case-analysis
  ;;;          of \verb$DEFINITION$.
  
  (AND (NOT (DA-GTERM.DEF.IS.VALUE DEFINITION))
       (GETF (DA-GTERM.ATTRIBUTES DEFINITION) 'RECURSION)))


(DEFUN DA-GTERM.DEF.MARK.TERMINATION (DEFINITION PROJECTIONS)

  ;;; Input:   a gterm, denoting a (part of a) definition, and a list of recursion orderings
  ;;; Effect:  inserts \verb$PROJECTIONS$ as the list of recursion orderings which are based
  ;;;          on the top-level case-analysis.
  ;;; Value:   undefined.

  (SETF (GETF (DA-GTERM.ATTRIBUTES DEFINITION) 'RECURSION) PROJECTIONS))


(DEFUN DA-GTERM.DEF.MAP.WITH.CONDS (DEFINITION APPLY.FCT &OPTIONAL CONDITIONS)
  
  ;;; input  : a definition, an apply function, which will
  ;;;          be applied to each specified case and  list of literals
  ;;; effect : \verb$APPLY.FCT$ is applied for each value of \verb$DEFINITION$
  
  (COND ((DA-GTERM.DEF.IS.VALUE DEFINITION)
	 (FUNCALL APPLY.FCT DEFINITION CONDITIONS))
	(T (MAPC #'(LAMBDA (DEF.TERM)
			   (DA-GTERM.DEF.MAP.WITH.CONDS (DA-GTERM.DEF.VALUE DEF.TERM)
							APPLY.FCT
							(APPEND CONDITIONS (DA-GTERM.DEF.CONDITION DEF.TERM))))
		 (DA-GTERM.TERMLIST DEFINITION)))))


(DEFUN DA-GTERM.DEF.MAPCAN.WITH.CONDS (DEFINITION APPLY.FCT &OPTIONAL CONDITIONS)
  
  ;;; input  : a definition, an apply function, which will
  ;;;          be applied to a an if.then.case and a list of literals
  ;;; effect : \verb$APPLY.FCT$ is applied for each value of \verb$DEFINITION$
  ;;; Value  : the concatenated results of \verb$APPLY.FCT$
  
  (COND ((DA-GTERM.DEF.IS.VALUE DEFINITION)
	 (FUNCALL APPLY.FCT DEFINITION CONDITIONS))
	(T (MAPCan #'(LAMBDA (DEF.TERM)
			     (DA-GTERM.DEF.MAPCAN.WITH.CONDS (DA-GTERM.DEF.VALUE DEF.TERM)
							     APPLY.FCT
							     (APPEND (DA-GTERM.DEF.CONDITION DEF.TERM) CONDITIONS)))
		   (DA-GTERM.TERMLIST DEFINITION)))))


(DEFUN DA-GTERM.DEF.REPLACE.WITH.CONDS (DEFINITION APPLY.FCT &OPTIONAL CONDITIONS)
  
  ;;; input  : a definition, an apply function, and a list of literals
  ;;; Effect : \verb$APPLY.FCT$ is applied for each value-slot of \verb$DEFINITION$
  ;;;          and each value-slot is replaced by the result of application.
  ;;; Value:   the changed \verb$DEFINITION$.
  
  (COND ((DA-GTERM.DEF.IS.VALUE DEFINITION)
	 (FUNCALL APPLY.FCT DEFINITION CONDITIONS))
	(T (MAPC #'(LAMBDA (DEF.TERM)
			   (SETF (DA-GTERM.DEF.VALUE DEF.TERM)
				 (DA-GTERM.DEF.REPLACE.WITH.CONDS 
				  (DA-GTERM.DEF.VALUE DEF.TERM)
				  APPLY.FCT
				  (APPEND CONDITIONS (DA-GTERM.DEF.CONDITION DEF.TERM)))))
		 (DA-GTERM.TERMLIST DEFINITION))
	   DEFINITION)))


;;;;;========================================================================================================
;;;;; Chapter 
;;;;; -------
;;;;;
;;;;; Functions to handle terms
;;;;;========================================================================================================


(DEFMACRO DA-TERM.IS (OBJECT)
  
  ;;; Input:  an object
  ;;; Value:  T, iff \verb$OBJECT$ is a simple term.
  
  `(TYPEP ,OBJECT 'TERM))


(DEFMACRO DA-TERM.CREATE (SYMBOL &OPTIONAL TERMLIST COLOURS ATTRIBUTES)
  
  ;;; Input:   a symbol, a list of terms (if symbol is a function), a colour and a list of attributes
  ;;; Value:   creates the denoted term.
  
  `(MAKE-TERM :SYMBOL ,SYMBOL :TERMLIST ,TERMLIST :COLOURS ,COLOURS :ATTRIBUTES ,ATTRIBUTES))


(DEFUN DA-TERM.COPY (TERM &OPTIONAL REPLACE.COLOUR COLOUR COL.KEY)
  
  ;;; Input:  a simple term
  ;;; Effect: copies this term and if \verb$REPLACE.COLOUR$ is T the colour of the copy is
  ;;;         either replaced by \verb$COLOUR$ or by new colour variables under indicator
  ;;;         \verb$COL.KEY$.
  
  (DA-TERM.CREATE (DA-TERM.SYMBOL TERM)
		  (MAPCAR #'(LAMBDA (SUBTERM)
				    (DA-TERM.COPY SUBTERM REPLACE.COLOUR COLOUR COL.KEY))
			  (DA-TERM.TERMLIST TERM))
		  (COND (REPLACE.COLOUR (OR COLOUR (LIST COL.KEY (DA-COLOUR.CREATE.VARIABLE))))
			(T (COPY-LIST (DA-TERM.COLOURS TERM))))
		  (COPY-TREE (DA-TERM.ATTRIBUTES TERM))))


(DEFMACRO DA-TERM.SORT (TERM)
  
  ;;; Input:  a term
  ;;; Value:  the sort of the term
  
  `(DA-SYMBOL.SORT (DA-TERM.SYMBOL ,TERM)))



(DEFUN DA-TERM.FUNCTION.OPEN (TERM SYMBOL)

  ;;; Input:   a term and an associative function-symbol
  ;;; Effect:  collects all arguments of \verb$SYMBOL$ in \verb$TERM$ regarding associativity
  ;;; Value:   the list of parameters
  
  (COND ((EQ (DA-TERM.SYMBOL TERM) SYMBOL)
	 (MAPCAN #'(LAMBDA (ARG) (DA-TERM.FUNCTION.OPEN ARG SYMBOL))
		 (DA-TERM.TERMLIST TERM)))
	(T (LIST TERM))))


(DEFUN DA-TERM.FUNCTION.CLOSURE (SYMBOL TERMLIST EXEPTION.VALUE &optional COLOUR.KEY)
  
  ;;; Input:   an associative function-symbol, a list of terms, a term and a key for colouring
  ;;; Effect:  computes a term with \verb$SYMBOL$ as top-level-symbol and \verb$TERMLIST$
  ;;;          as its parameters or a nested call of \verb$SYMBOL$ with \verb$TERMLIST$
  ;;;          regarding the arity of \verb$SYMBOL$. In case \verb$TERMLIST$ is empty the
  ;;;          \verb$EXEPTION.VALUE$ is returned. In case \verb$ COLOUR.KEY$ is not nil
  ;;;          the resulting term is coloured fade.
  ;;; Value:   the created term

  (COND ((NULL TERMLIST) EXEPTION.VALUE)
	((NULL (CDR TERMLIST)) (CAR TERMLIST))
	(T (DA-TERM.CREATE SYMBOL (LIST (CAR TERMLIST)
					(DA-TERM.FUNCTION.CLOSURE SYMBOL (CDR TERMLIST)
								  EXEPTION.VALUE COLOUR.KEY))
			   (COND (COLOUR.KEY (LIST COLOUR.KEY (DA-COLOUR.FADED))))))))


(DEFUN DA-TERM.IS.MOST.GENERAL (TERM &OPTIONAL EXEPTIONS)
  
  ;;; Input:   a term
  ;;; Effect:  see value
  ;;; Value:   T, if all arguments of \verb$TERM$ are pairwise different variables.
  ;;;          if \verb$EXEPTIONS$ is T and exactly one argument is non variable then the position of it
  
  (LET (USED.VARS POSITION (COUNTER 0))
       (COND ((EVERY #'(LAMBDA (SUBTERM)
			       (INCF COUNTER)
			       (COND ((DA-VARIABLE.IS (DA-TERM.SYMBOL SUBTERM))
				      (COND ((NOT (MEMBER (DA-TERM.SYMBOL SUBTERM) USED.VARS))
					     (PUSH (DA-TERM.SYMBOL SUBTERM) USED.VARS))))
				     (EXEPTIONS (SETQ EXEPTIONS NIL)
						(SETQ POSITION COUNTER))))
		     (DA-TERM.TERMLIST TERM))
	      (COND (POSITION (VALUES POSITION USED.VARS))
		    (T (VALUES T USED.VARS)))))))


(DEFUN DA-TERM.IS.CONSTRUCTOR.GROUND (TERM)
  
  ;;; edited : 12.02.93 by CS
  ;;; input  : a term
  ;;; value  : either T or NIL, depending whether TERM consists only of constructor functions

  (AND (DA-FUNCTION.IS (DA-TERM.SYMBOL TERM))
       (DA-FUNCTION.IS.CONSTRUCTOR (DA-TERM.SYMBOL TERM))
       (EVERY #'DA-TERM.IS.CONSTRUCTOR.GROUND (DA-TERM.TERMLIST TERM))))


(DEFUN DA=TERM.PRINT (TERM STREAM DEPTH)
  
  ;;; Input:  a term
  ;;; Effect: prints a printed represention of \verb$TERM$ on \verb$STREAM$
  ;;; Value:  undefined.
  
  (COND ((AND *PRINT-LEVEL* (> DEPTH *PRINT-LEVEL*))
	 (FORMAT STREAM "..."))
	(T (PRINC (DA-TERM.SYMBOL TERM) STREAM)
	   (COND ((AND DA*GTERM.COLOUR.PRINTING (DA-TERM.COLOURS TERM)) (FORMAT STREAM ":~A" (DA-TERM.COLOURS TERM))))
	   (COND ((DA-TERM.TERMLIST TERM) (FORMAT STREAM "~A" (DA-TERM.TERMLIST TERM)))))))


(DEFUN DA-TERM.REVERSE.ARGLIST (TERM)
  
  ;;; Input:   a term
  ;;; Value:   NIL if \verb$TERM$ a constant or variable, else the term with reversed toplevel argument list 
  
  (DA-TERM.CREATE (DA-TERM.SYMBOL TERM)
		  (DA-TERM.TERMLIST (REVERSE (DA-TERM.TERMLIST TERM)))))


(DEFUN DA-TERM.APPLY.MATCH.SUBST (TERM SUBST)

  ;;; Input:   a term and a substitution
  ;;; Effect:  applies \verb$SUBST$ on \verb$TERM$ and reduces \verb$TERM$ by structural rules.

  (DB=GTERM.REDUCE (UNI-SUBST.APPLY SUBST TERM T)))


(DEFUN DA=TERM.APPLY.MATCH.SUBST (GTERM)

  ;;; Input:   a term
  ;;; Effect:  reduces \verb$GTERM$ by structural equations like $p(s(x)) = x$.
  ;;; Value:   the reduced term
  
  (SETF (DA-GTERM.TERMLIST GTERM)
	(MAPCAR #'(LAMBDA (SUBTERM) (DA=TERM.APPLY.MATCH.SUBST SUBTERM))
		(DA-GTERM.TERMLIST GTERM)))
  (COND ((AND (DA-FUNCTION.IS (DA-GTERM.SYMBOL GTERM))
	      (DA-FUNCTION.IS.SELECTOR (DA-GTERM.SYMBOL GTERM))
	      (EQ (DA-SORT.CONSTRUCTOR.OF.SELECTOR (DA-GTERM.SYMBOL GTERM))
		  (DA-GTERM.SYMBOL (CAR (DA-GTERM.TERMLIST GTERM)))))
	 (NTH (POSITION (DA-GTERM.SYMBOL GTERM)
			(DA-SORT.SELECTORS.OF.CONSTRUCTOR (DA-GTERM.SYMBOL (CAR (DA-GTERM.TERMLIST GTERM)))))
	      (DA-GTERM.TERMLIST (CAR (DA-GTERM.TERMLIST GTERM)))))
	(T GTERM)))

;;;;;
;;;;;========================================================================================================
;;;;; Chapter 
;;;;; -------
;;;;;
;;;;; Functions to handle the datastructure LITERAL
;;;;;========================================================================================================


(DEFUN DA-LITERAL.PRINT (LITERAL STREAM &OPTIONAL (DEPTH 0))
  
  ;;; Input:  a literal
  ;;; Effect: prints a printed represention of \verb$LITERAL$ on \verb$STREAM$.
  ;;; Value:  undefined.
  
  (DA=LITERAL.PRINT LITERAL STREAM DEPTH))


(DEFUN DA-LITERAL.IS (LITERAL)
  
  ;;; edited at 30-JUL-85 16:42:02
  ;;; Input:  a sexpression.
  ;;; Value:  T, if \verb$LITERAL$ denotes a literal.
  
  (EQ (TYPE-OF LITERAL) 'LITERAL))


(DEFMACRO DA-LITERAL.CREATE (SIGN PREDICATE TERMLIST &OPTIONAL ATTRIBUTES COLOURS PNAME)
  
  ;;; Input:  a sign, a predicate symbol, a list of terms and a arbitrary sexpression.
  ;;; Value:  a new literal created by the given components.
  
  `(MAKE-LITERAL :SIGN ,SIGN :SYMBOL ,PREDICATE :TERMLIST ,TERMLIST
		 :ATTRIBUTES ,ATTRIBUTES :COLOURS ,COLOURS :PNAME ,PNAME))


(DEFUN DA-LITERAL.COPY (LITERAL &OPTIONAL REPLACE.COLOUR COLOURS COL.KEY)
  
  ;;; Input:  a literal
  ;;; Value:  a copy of \verb$LITERAL$, where also the slots termlist and property are copied.

  (LET ((PROPERTIES (COPY-TREE (DA-LITERAL.ATTRIBUTES LITERAL))))
    (COND ((GETF PROPERTIES 'ACTIVE)
	   (SETF (GETF PROPERTIES 'ACTIVE) NIL)))
    (MAKE-LITERAL :SIGN (DA-LITERAL.SIGN LITERAL)
		  :SYMBOL (DA-LITERAL.SYMBOL LITERAL)
		  :TERMLIST (MAPCAR #'(LAMBDA (OBJECT)
					(DA-TERM.COPY OBJECT REPLACE.COLOUR COLOURS COL.KEY))
				    (DA-LITERAL.TERMLIST LITERAL))
		  :ATTRIBUTES PROPERTIES
		  :COLOURS (COND (REPLACE.COLOUR (OR COLOURS (LIST COL.KEY (DA-COLOUR.CREATE.VARIABLE))))
				 (T (COPY-TREE (DA-LITERAL.COLOURS LITERAL)))))))


(DEFMACRO DA-LITERAL.IS.NEGATIVE (LIT)
  
  ;;; Input:  a literal
  ;;; Value: T, iff \verb$LIT$ has negative sign
  
  `(DA-SIGN.IS.NEGATIVE (DA-LITERAL.SIGN ,LIT)))


(DEFMACRO DA-LITERAL.IS.POSITIVE (LIT)
  
  ;;; Input:  a literal
  ;;; Value:  T, iff \verb$LIT$ has positive sign
  
  `(DA-SIGN.IS.POSITIVE (DA-LITERAL.SIGN ,LIT)))


(DEFMACRO DA-LITERAL.IS.EQUALITY (LIT)
  
  ;;; Input:  a literal
  ;;; Value:  T, iff \verb$LIT$ has the equality symbol as predicate
  
  `(DA-PREDICATE.IS.EQUALITY (DA-LITERAL.SYMBOL ,LIT)))


(DEFUN DA-LITERAL.IS.EQUATION (LITERAL)
  
  ;;; Input:  a literal
  ;;; Value:  T, if \verb$LITERAL$ denotes an equation
  
  (AND (DA-LITERAL.IS.POSITIVE LITERAL)
       (DA-PREDICATE.IS.EQUALITY (DA-LITERAL.SYMBOL LITERAL))))


(DEFUN DA-LITERAL.IS.NEGATED.EQUATION (LITERAL)
  
  ;;; Input:  a literal
  ;;; Value:  T, if \verb$LITERAL$ denotes a negated equation
  
  (AND (DA-LITERAL.IS.NEGATIVE LITERAL)
       (da-PREDICATE.IS.EQUALITY (DA-LITERAL.SYMBOL LITERAL))))



(DEFMACRO DA-LITERAL.TRUE ()
  
  ;;; Value:   the true-literal
  
  `(DP-LITERAL.TRUE))


(DEFUN DA-LITERAL.IS.TRUE (LITERAL)
  
  ;;; edited at 30-JUL-85 16:28:55
  ;;; Input:  a literal 
  ;;; Value:  Returns T, if \verb$LITERAL$ is equal to TRUE.
  
  (AND (DA-LITERAL.IS LITERAL)
       (DA-LITERAL.IS.POSITIVE LITERAL)
       (DA-PREDICATE.IS.TRUE (DA-LITERAL.SYMBOL LITERAL))))


(DEFUN DA-LITERAL.IS.FALSE (LITERAL)
  
  ;;; edited at 30-JUL-85 16:30:19
  ;;; Input:  a literal 
  ;;; Value:  Returns T, if \verb$LITERAL$ is equal to FALSE.
  
  (AND (DA-LITERAL.IS LITERAL)
       (DA-LITERAL.IS.POSITIVE LITERAL)
       (DA-PREDICATE.IS.FALSE (DA-LITERAL.SYMBOL LITERAL))))


(DEFMACRO DA-LITERAL.FALSE ()
  
  ;;; Value:   the false-literal
  
  `(DP-LITERAL.FALSE))



(DEFUN DA-LITERALS.MATCH.SUBST (LITERALS)
  ;;; Input: a list of literals
  ;;; Value: a substitution which is derived from the match literals of \verb$LITERALS$

  (LET (SEL.TERM SUBST VALUE)
    (MAPC #'(LAMBDA (LITERAL)
	      (COND ((AND (DA-LITERAL.IS LITERAL)
			  (DA-LITERAL.IS.MATCH LITERAL))
		     (SETQ VALUE (SECOND (DA-LITERAL.TERMLIST LITERAL)))
		     (SETQ SEL.TERM (CAR (DA-LITERAL.TERMLIST LITERAL)))
		     (COND ((OR (NULL (DA-TERM.TERMLIST VALUE))
				(SOME #'(LAMBDA (TAF)
					  (AND TAF (DA-FUNCTION.IS.SELECTOR
						    (DA-TERM.SYMBOL (DA-ACCESS (CDR TAF) VALUE)))))
				      (DA-GTERM.OCCURS.IN.GTERM SEL.TERM VALUE)))
			    (SETQ SUBST (DA=LITERAL.MATCH.COMPUTE.SUBST LITERAL SUBST)))))))
	  LITERALS)
    SUBST))


(DEFUN DA=LITERAL.MATCH.COMPUTE.SUBST (LITERAL SUBST)

  ;;; Input:  a substitution and a match-literal
  ;;; Effect: updates \verb$SUBST$ by the replacement of the selectorterms defined by \verb$LITERAL$.
  ;;; Value:  the adapted substitution.
  
  (LET ((SEL.TERM (CAR (DA-LITERAL.TERMLIST LITERAL)))
	(TERM (DA-FUNCTION.CREATE.TERM (DA-TERM.SYMBOL (SECOND (DA-LITERAL.TERMLIST LITERAL))))))
       (COND ((NOT (DA-VARIABLE.IS (DA-TERM.SYMBOL SEL.TERM)))
	      (SETQ SEL.TERM (DB=GTERM.REDUCE (UNI-SUBST.APPLY SUBST SEL.TERM T)))))
       (CAR (UNI-SUBST.MERGE (CAR (UNI-TERM.MATCH SEL.TERM TERM T)) SUBST))))


(DEFUN DA-LITERAL.NEGATE (LITERAL)  ;; --> ENTFAELLT ZUGUNSTEN DA-TERM.NEGATE !!!
  
  ;;; input  : a literal
  ;;; value  : the destructively negated \verb$LITERAL$
  
  (COND ((DA-LITERAL.IS.TRUE LITERAL) (DA-LITERAL.FALSE))
	((DA-LITERAL.IS.FALSE LITERAL) (DA-LITERAL.TRUE))
	(T (SETF (DA-LITERAL.SIGN LITERAL) (DA-SIGN.OTHER.SIGN (DA-LITERAL.SIGN LITERAL)))
	   LITERAL)))



(DEFUN DA=LITERAL.PRINT (LITERAL STREAM DEPTH)
  
  ;;; Input:  a literal, an output-stream, and an integer
  ;;; Effect: prints \verb$LITERAL$ on \verb$STREAM$ if \verb$DEPTH$ is less or equal than
  ;;;         \verb$*PRINT-LEVEL*$, else \verb$#$ is printed.
  ;;; Value:  undefined.
  
  (COND ((AND *PRINT-LEVEL* (> DEPTH *PRINT-LEVEL*)) (FORMAT STREAM "..."))
	((DA-PREDICATE.IS.EQUALITY (DA-LITERAL.SYMBOL LITERAL))
	 (FORMAT STREAM "~A ~:[=~;=/=~] ~A"
		 (CAR (DA-LITERAL.TERMLIST LITERAL))
		 (DA-SIGN.IS.NEGATIVE (DA-LITERAL.SIGN LITERAL))
		 (SECOND (DA-LITERAL.TERMLIST LITERAL))))
	(T (FORMAT STREAM "~:[~;Not_~]~A~A"
		   (DA-SIGN.IS.NEGATIVE (DA-LITERAL.SIGN LITERAL))
		   (DA-LITERAL.SYMBOL LITERAL)
		   (cond ((DA-LITERAL.TERMLIST LITERAL))
			 (t ""))))))


;;; match

(DEFUN DA-LITERAL.DENOTES.MATCH (LITERAL &OPTIONAL (SIGN (DA-SIGN.MINUS)))
  
  ;;; Input:  a literal
  ;;; Effect: checks whether \verb$LITERAL$ is a (negated) equality which contain structural information, e.g. describes out of
  ;;;         which constructors the left term is build up.
  ;;; Value:  a multiple value: the term, a symbol denoting the corresponding case, and a flag, whether the information
  ;;;         is negated or not.
  
  (COND ((DA-PREDICATE.IS.EQUALITY (DA-LITERAL.SYMBOL LITERAL))
	 (LET ((LEFT (CAR (DA-LITERAL.TERMLIST LITERAL))) (RIGHT (SECOND (DA-LITERAL.TERMLIST LITERAL))))
	      (COND ((AND (DA-SYMBOL.HAS.ATTRIBUTE (DA-TERM.SYMBOL RIGHT) 'STRUCTURE)
			  (OR (EQ SIGN (DA-LITERAL.SIGN LITERAL))
			      (DA=LITERAL.MATCH.TERMLIST.ARE.SELECTORS LEFT RIGHT)))
		     (VALUES LEFT (DA-TERM.SYMBOL RIGHT) (NEQ SIGN (DA-LITERAL.SIGN LITERAL))))
		    ((AND (MEMBER (DA-TERM.SORT RIGHT) (DA-SORT.BASE.SORTS (DA-TERM.SORT LEFT)))
			  (OR (EQ SIGN (DA-LITERAL.SIGN LITERAL))
			      (AND (DA-FUNCTION.IS.INDEX (DA-TERM.SYMBOL RIGHT))
				   (UNI-TERM.ARE.EQUAL (CAR (DA-TERM.TERMLIST RIGHT)) LEFT))))
		     (VALUES LEFT (DA-SORT.INDEX.FCT.OF.SORT (DA-TERM.SORT LEFT) (DA-TERM.SORT RIGHT))
			     (NEQ SIGN (DA-LITERAL.SIGN LITERAL)))))))))


(DEFUN DA-LITERAL.IS.NORMALIZED.MATCH (LITERAL &optional (SIGN (da-sign.plus)))

  ;;; Input:  a literal

  (COND ((AND (DA-PREDICATE.IS.EQUALITY (DA-LITERAL.SYMBOL LITERAL))
	      (EQ SIGN (DA-LITERAL.SIGN LITERAL)))
	 (LET ((LEFT (CAR (DA-LITERAL.TERMLIST LITERAL))) (RIGHT (SECOND (DA-LITERAL.TERMLIST LITERAL))))
	   (COND ((AND (DA-SYMBOL.HAS.ATTRIBUTE (DA-TERM.SYMBOL RIGHT) 'STRUCTURE)
		       (DA=LITERAL.MATCH.TERMLIST.ARE.SELECTORS LEFT RIGHT))
		  (VALUES LEFT (DA-TERM.SYMBOL RIGHT)))
		 ((AND (MEMBER (DA-TERM.SORT RIGHT) (DA-SORT.BASE.SORTS (DA-TERM.SORT LEFT)))
		       (AND (DA-FUNCTION.IS.INDEX (DA-TERM.SYMBOL RIGHT))
			    (UNI-TERM.ARE.EQUAL (CAR (DA-TERM.TERMLIST RIGHT)) LEFT)))
		  (VALUES LEFT (DA-SORT.INDEX.FCT.OF.SORT (DA-TERM.SORT LEFT) (DA-TERM.SORT RIGHT)))))))))


(DEFUN DA=LITERAL.MATCH.TERMLIST.ARE.SELECTORS (LEFT RIGHT)
  
  (OR (AND (NULL (DA-TERM.TERMLIST RIGHT))
	   (EQ (DA-TERM.SORT LEFT) (DA-TERM.SORT RIGHT)))
      (EVERY #'(LAMBDA (SELECTOR TERM)
		       (AND (EQ (DA-TERM.SYMBOL TERM) SELECTOR)
			    (UNI-TERM.ARE.EQUAL (CAR (DA-TERM.TERMLIST TERM)) LEFT)))
	     (DA-SORT.SELECTORS.OF.CONSTRUCTOR (DA-TERM.SYMBOL RIGHT))
	     (DA-TERM.TERMLIST RIGHT))))


(DEFMACRO DA-LITERAL.IS.MATCH (LITERAL)
  
  ;;; Input:  a literal
  ;;; Value:  T, if \verb$LITERAL$ is recognized as match-literal.
  
  `(MEMBER 'MATCH (GETF (DA-LITERAL.ATTRIBUTES ,LITERAL) 'KIND)))



;;;;;
;;;;;========================================================================================================
;;;;; Chapter 
;;;;; -------
;;;;;
;;;;; Functions to handle the datastructure FORMULA
;;;;;========================================================================================================


(DEFMACRO DA-FORMULA.IS (FORM)
  
  ;;; edited at 30-JUL-85 16:45:03
  ;;; Input:  a sexpression
  ;;; Value:  T, if \verb$FORMULA$ is a prefix-formula but no literal.
  
  `(TYPEP ,FORM 'FORMULA))


(DEFUN DA=FORMULA.PRINT (FORMULA STREAM DEPTH)
  (COND ((AND *PRINT-LEVEL* (> DEPTH *PRINT-LEVEL*)) (FORMAT STREAM "..."))
	(T (CASE (DA-FORMULA.SYMBOL FORMULA)
		 ((ALL EX) (FORMAT STREAM "(~A ~A ~A)" (DA-FORMULA.SYMBOL FORMULA) (CAR (DA-FORMULA.TERMLIST FORMULA))
				   (SECOND (DA-FORMULA.TERMLIST FORMULA))))
		 ((AND OR IMPL EQV NOT) (FORMAT STREAM "(~A ~{~A ~})" (DA-FORMULA.SYMBOL FORMULA) (DA-FORMULA.TERMLIST FORMULA)))
		 (T (FORMAT STREAM "(~A ~A)" (DA-FORMULA.SYMBOL FORMULA) (DA-FORMULA.TERMLIST FORMULA)))))))


(DEFMACRO DA-FORMULA.CREATE (OP TERMLIST &OPTIONAL COLOURS ATTRIBUTES)
  
  ;;; Input:   an operator (such as \verb$AND$, \verb$OR$, \verb$ALL$, \verb$EX$, \verb$IMPL$, \verb$EQV$, \verb$NOT$)
  ;;;          and two formulas
  ;;; Value:   creates a new formula \verb$(OP LEFT RIGHT)$
  
  `(MAKE-FORMULA :SYMBOL ,OP :TERMLIST ,TERMLIST :COLOURS ,COLOURS :ATTRIBUTES ,ATTRIBUTES))


(DEFUN DA-FORMULA.COPY (FORMULA &OPTIONAL REPLACE.COLOUR COLOURS COL.KEY)
  
  ;;; Input:  a simple term
  ;;; Effect: copies this term and if \verb$REPLACE.COLOUR$ is T the colour of the copy is
  ;;;         either replaced by \verb$COLOUR$ or by new colour variables.
  
  (LET ((ATTR (COPY-TREE (DA-FORMULA.ATTRIBUTES FORMULA))))
    (COND ((GETF ATTR 'ACTIVE)
	   (SETF (GETF ATTR 'ACTIVE) NIL)))
    (DA-FORMULA.CREATE (DA-FORMULA.SYMBOL FORMULA)
		       (MAPCAR #'(LAMBDA (SUBTERM)
				   (cond ((da-gterm.is subterm)   ; in case of quantors here are variables
					  (DA-GTERM.COPY SUBTERM REPLACE.COLOUR COLOURS COL.KEY))
					 (T SUBTERM)))
			       (DA-FORMULA.TERMLIST FORMULA))
		       (COND (REPLACE.COLOUR (OR COLOURS (LIST COL.KEY (DA-COLOUR.CREATE.VARIABLE))))
			     (T (COPY-LIST (DA-GTERM.COLOURS FORMULA))))
		       ATTR)))


(DEFUN DA-FORMULA.IS.TRUE (FORMULA)
  
  ;;; Input:  a formula
  ;;; Value:  T if the formula is the true literal
  
  (AND (DA-LITERAL.IS FORMULA) (DA-LITERAL.IS.TRUE FORMULA)))


(DEFUN DA-FORMULA.IS.FALSE (FORMULA)
  
  ;;; Input:  a formula
  ;;; Value:  T if the formula is the false literal
  
  (AND (DA-LITERAL.IS FORMULA) (DA-LITERAL.IS.FALSE FORMULA)))


(DEFUN DA-FORMULA.MAP.LITERALS (FORMULA APPLY.FCT)
  
  ;;; Input  :  a formula and a functional
  ;;; Effect :  walks through \verb$FORMULA$ and applies \verb$APPLY.FCT$ to each literal in \verb$FORMULA$.
  ;;; Value  :  undefined
  
  (COND ((DA-LITERAL.IS FORMULA) (FUNCALL APPLY.FCT FORMULA))
	((MEMBER (DA-FORMULA.SYMBOL FORMULA) '(AND OR IMPL EQV NOT))
	 (MAPC #'(lambda(term) (DA-FORMULA.MAP.LITERALS term apply.fct))
	       (DA-FORMULA.TERMLIST FORMULA)))
	((MEMBER (DA-FORMULA.SYMBOL FORMULA) '(ALL EX))
	 (DA-FORMULA.MAP.LITERALS (SECOND (DA-FORMULA.TERMLIST FORMULA)) APPLY.FCT))))


(DEFUN DA-FORMULA.CHANGE.LITERALS (FORMULA APPLY.FCT)
  
  ;;; Input  :  a formula and a functional
  ;;; Effect :  walks through \verb$FORMULA$ and applies \verb$APPLY.FCT$ to each literal in \verb$FORMULA$.
  ;;;           the literals are replaced by the result of these applications.
  ;;; Value  :  the destructively changed formula.
  
  (COND ((DA-LITERAL.IS FORMULA) (FUNCALL APPLY.FCT FORMULA))
	((MEMBER (DA-FORMULA.SYMBOL FORMULA) '(AND OR IMPL EQV NOT))
	 (MAPL #'(LAMBDA (SUB.FORM)
			 (SETF (CAR SUB.FORM) (DA-FORMULA.CHANGE.LITERALS (CAR SUB.FORM) APPLY.FCT)))
	       (DA-FORMULA.TERMLIST FORMULA))
	 FORMULA)
	((MEMBER (DA-FORMULA.SYMBOL FORMULA) '(ALL EX))
	 (SETF (SECOND (DA-FORMULA.TERMLIST FORMULA))
	       (DA-FORMULA.CHANGE.LITERALS (SECOND (DA-FORMULA.TERMLIST FORMULA)) APPLY.FCT))
	 FORMULA)))


(DEFUN DA-FORMULA.QUANTIFICATION.CLOSURE (QUANTOR VARIABLE.LIST FORMULA)
  
  ;;; edited at 30-JUL-85 16:49:23
  ;;; Input:  \verb$ALL$ or \verb$EX$, a list of variablesymbols, and a
  ;;;         sexpression denoting a formula
  ;;; Effect: see value.
  ;;; Value:  Returns the quantification-closure of the given formula w.r.t.
  ;;;         \verb$QUANTOR$ and \verb$VARIABLE.LIST$.
  
  (LET ((RESULT FORMULA))
       (MAPC #'(LAMBDA (VARIABLE)
		       (SETQ RESULT (DA-FORMULA.CREATE QUANTOR (LIST VARIABLE RESULT))))
	     (REVERSE VARIABLE.LIST))
       RESULT))


(DEFUN DA-FORMULA.JUNCTION.CLOSURE (JUNCTOR FORMULAS)
  
  ;;; edited at 30-JUL-85 16:52:34
  ;;; Input:  an atom \verb$AND$, \verb$OR$ or \verb$IMPL$ and
  ;;;         a list of formulas
  ;;; Effect: see value.
  ;;; Value:  The junction-closure of the given formulas w.r.t. \verb$QUANTOR$ and \verb$FORMULAS$.
  
  (SETQ FORMULAS (REVERSE FORMULAS))
  (LET ((CODE (CAR FORMULAS)))
       (MAPC #'(LAMBDA (FORMULA)
		       (SETQ CODE (DA-FORMULA.CREATE JUNCTOR (LIST FORMULA CODE))))
	     (CDR FORMULAS))
       (COND (CODE)
	     ((EQ JUNCTOR 'AND) (DA-LITERAL.TRUE))
	     (T (DA-LITERAL.FALSE)))))


(DEFUN DA-FORMULA.IMPL.CLOSURE (FORMULA1 FORMULA2)
  
  ;;; Input:  two formulas
  ;;; Value:  a simplified formula equivalent to \verb$($ \verb$IMPL$ \verb$FORMULA1$ \verb$FORMULA2$ \verb$)$
  ;;; Note:   parts of the old formulas may occur in the result.
  
  (COND ((DA-LITERAL.IS.FALSE FORMULA1) (DA-LITERAL.TRUE))
	((DA-LITERAL.IS.TRUE FORMULA1) FORMULA2)
	((DA-LITERAL.IS.TRUE FORMULA2) FORMULA2)
	((DA-LITERAL.IS.FALSE FORMULA2) (DA-FORMULA.NEGATE FORMULA1))
	(T (DA-FORMULA.CREATE 'IMPL (LIST FORMULA1 FORMULA2)))))



(DEFUN DA-FORMULA.QUANTIFICATION.OPEN (QUANTOR FORMULA)
  
  ;;; edited at 30-JUL-85 16:55:37
  ;;; Input: \verb$ALL$ or \verb$EX$ and a formula.
  ;;; Effect: The inverse of DA-FORMULA.QUANTIFICATION.CLOSURE.
  ;;; Value:  A dotted pair \verb$x$, where \verb$(car x)$ is a list of variablesymbols and \verb$(cdr x)$ is a  formula.
  ;;; Note:   parts of the old formulas may occur in the result.
  
  (COND ((AND (DA-FORMULA.IS FORMULA) (EQ (DA-FORMULA.SYMBOL FORMULA) QUANTOR))
	 (LET ((RESULT (DA-FORMULA.QUANTIFICATION.OPEN QUANTOR (SECOND (DA-FORMULA.TERMLIST FORMULA)))))
	      (PUSH (CAR (DA-FORMULA.TERMLIST FORMULA)) (CAR RESULT))
	      RESULT))
	(T (CONS NIL FORMULA))))


(DEFUN DA-FORMULA.JUNCTION.OPEN (JUNCTOR FORMULA)
  
  ;;; edited at 30-JUL-85 16:57:31
  ;;; Input:  an atom \verb$AND$, \verb$OR$ or \verb$IMPL$ and a formula.
  ;;; Effect: The inverse function of \verb$DA-FORMULA.JUNCTION.CLOSURE$.
  ;;; Value:  A dotted pair \verb$x$, where \verb$(car x)$ is a list of variablesymbols and \verb$(cdr x)$ is a list of formulas.
  ;;; Note:   parts of the old formulas may occur in the result.
  
  (COND ((AND (DA-GTERM.IS FORMULA) (EQ (DA-GTERM.SYMBOL FORMULA) JUNCTOR))
	 (MAPCAN #'(LAMBDA (SUB.FORM)
		     (DA-FORMULA.JUNCTION.OPEN JUNCTOR SUB.FORM))
		 (DA-GTERM.TERMLIST FORMULA)))
	((AND (EQ JUNCTOR 'AND) (DA-FORMULA.IS.TRUE FORMULA)) NIL)
	((AND (EQ JUNCTOR 'OR) (DA-FORMULA.IS.FALSE FORMULA)) NIL)
	(T (LIST FORMULA))))


(DEFUN DA-FORMULA.NEGATE (FORMULA)
  
  ;;; edited  5. April 89 by mp
  ;;; Input : a formula
  ;;; Value : a simplified formula equivalent to \verb$(NOT FORMULA)$.
  ;;; Note:   parts of the old formulas may occur in the result.
  
  (COND ((DA-LITERAL.IS FORMULA)
	 (DA-LITERAL.NEGATE (DA-LITERAL.COPY FORMULA)))
	(T
	 (COND ((EQ (DA-GTERM.SYMBOL FORMULA) 'NOT) 
		(CAR (DA-GTERM.TERMLIST FORMULA)))
	       (T (DA-FORMULA.CREATE 'NOT (LIST FORMULA)))))))


(DEFUN DA-FORMULA.NEGATE.AND.NORMALIZE (FORMULA)
  
  ;;; edited  5. April 89 by mp
  ;;; Input : a formula
  ;;; Value : a simplified formula equivalent to \verb$(NOT FORMULA)$.
  ;;; Note:   parts of the old formulas may occur in the result.
  
  (COND ((DA-LITERAL.IS FORMULA)
	 (DA-LITERAL.NEGATE (DA-LITERAL.COPY FORMULA)))
	((EQ (DA-GTERM.SYMBOL FORMULA) 'NOT) 
	 (CAR (DA-GTERM.TERMLIST FORMULA)))
	((EQ (DA-GTERM.SYMBOL FORMULA) 'AND)
	 (DA-GTERM.CREATE 'OR (MAPCAR #'(LAMBDA (FOR) (DA-FORMULA.NEGATE.AND.NORMALIZE FOR))
				      (DA-GTERM.TERMLIST FORMULA))))
	((EQ (DA-GTERM.SYMBOL FORMULA) 'OR)
	 (DA-GTERM.CREATE 'AND (MAPCAR #'(LAMBDA (FOR) (DA-FORMULA.NEGATE.AND.NORMALIZE FOR))
				       (DA-GTERM.TERMLIST FORMULA))))
	(T (DA-FORMULA.CREATE 'NOT (LIST FORMULA)))))


(DEFUN DA-FORMUAL.MOVE.NEGATION.INSIDE (FORMULA)

  (COND ((EQ (DA-GTERM.SYMBOL FORMULA) 'NOT)
	 (DA-FORMULA.NEGATE.AND.NORMALIZE (CAR (DA-GTERM.TERMLIST FORMULA))))
	((MEMBER (DA-GTERM.SYMBOL FORMULA) '(OR AND))
	 (DA-GTERM.CREATE (DA-GTERM.SYMBOL FORMULA)
			  (MAPCAR #'(LAMBDA (FOR) (DA-FORMUAL.MOVE.NEGATION.INSIDE FOR))
				  (DA-GTERM.TERMLIST FORMULA))))
	(T FORMULA)))
	


(DEFMACRO DA-MODIFIER.INPUT (MODIFIER)

  ;;; Value:  the left hand side of the rule

  `(DA-MODFRAME.INPUT (DA-MODIFIER.MODFRAME ,MODIFIER)))


(DEFMACRO DA-MODIFIER.VALUE (MODIFIER)

  ;;; Input:  a  modifier
  ;;; Value:  the right hand side of the rule

  `(DA-MODFRAME.VALUE (DA-MODIFIER.MODFRAME ,MODIFIER)))


(DEFMACRO DA-MODIFIER.CONDITION (MODIFIER)

  ;;; Input:  a  modifier
  ;;; Value:  the right hand side of the rule

  `(DA-MODFRAME.CONDITION (DA-MODIFIER.MODFRAME ,MODIFIER)))


(DEFMACRO DA-MODIFIER.GTERM (MODIFIER)

  ;;; Input:  a  modifier
  ;;; Value:  the top-level gterm of the rule

  `(DA-MODFRAME.GTERM (DA-MODIFIER.MODFRAME ,MODIFIER)))


(DEFMACRO DA-MODIFIER.TAF (MODIFIER)

  ;;; Input:  a  modifier
  ;;; Value:  the term access function from top-level to the input

  `(DA-MODFRAME.TAF (DA-MODIFIER.MODFRAME ,MODIFIER)))


(DEFMACRO DA-MODIFIER.PNAME (MODIFIER)

  ;;; Input:  a  modifier
  ;;; Value:  the name of the rule

  `(DA-MODFRAME.PNAME (DA-MODIFIER.MODFRAME ,MODIFIER)))


(DEFUN DA-MODIFIER.DEFINING.INPUT (MODIFIER)

  ;;; Input:  a  modifier
  ;;; Value:  T iff the modifier is part of the activated database

  (DA-GTERM.DEFINING.INPUT (DA-MODIFIER.GTERM MODIFIER)))


(DEFMACRO DA-CMODIFIER.IS (EXPRESSION)
  
  ;;; edited    : 03.02.1994
  ;;; input     : an expression
  ;;; value(s)  : T, if the expression is a \verb$DA-CMODIFIER.$

  `(TYPEP ,EXPRESSION 'DA*COLOURED.MODIFIER))


(DEFUN DA-MODIFIER.IS (EXPRESSION)

  ;;; edited    : 03.02.1994
  ;;; input     : an expression
  ;;; value(s)  : T, if the expression is either a \verb$DA-MODIFIER$
  ;;;             or a \verb$DA-CMODIFIER.$

  (OR (DA-CMODIFIER.IS EXPRESSION)
      (TYPEP EXPRESSION 'DA*MODIFIER)))


(DEFMACRO DA-CMODIFIER.INPUT (MODIFIER)

  ;;; Value:  the left hand side of the rule

  `(DA-MODFRAME.INPUT (DA-CMODIFIER.MODFRAME ,MODIFIER)))


(DEFMACRO DA-CMODIFIER.VALUE (MODIFIER)

  ;;; Input:  a  modifier
  ;;; Value:  the right hand side of the rule

  `(DA-MODFRAME.VALUE (DA-CMODIFIER.MODFRAME ,MODIFIER)))


(DEFMACRO DA-CMODIFIER.CONDITION (MODIFIER)

  ;;; Input:  a  modifier
  ;;; Value:  the right hand side of the rule

  `(DA-MODFRAME.CONDITION (DA-CMODIFIER.MODFRAME ,MODIFIER)))


(DEFMACRO DA-CMODIFIER.GTERM (MODIFIER)

  ;;; Input:  a  modifier
  ;;; Value:  the top-level gterm of the rule

  `(DA-MODFRAME.GTERM (DA-CMODIFIER.MODFRAME ,MODIFIER)))


(DEFMACRO DA-CMODIFIER.TAF (MODIFIER)

  ;;; Input:  a  modifier
  ;;; Value:  the term access function from top-level to the input

  `(DA-MODFRAME.TAF (DA-CMODIFIER.MODFRAME ,MODIFIER)))


(DEFMACRO DA-CMODIFIER.PNAME (MODIFIER)

  ;;; Input:  a  modifier
  ;;; Value:  the name of the rule

  `(DA-MODFRAME.PNAME (DA-CMODIFIER.MODFRAME ,MODIFIER)))


(DEFUN DA-MODIFIER.INVERSE (MODIFIER)

  ;;; Input:  a modifier denoting an equality
  ;;; Value:  a modifier which reverses the the original one
  
  (LET* ((GTERM (DA-MODFRAME.GTERM (DA-MODIFIER.MODFRAME MODIFIER)))
	 (TAF (DA-MODFRAME.TAF (DA-MODIFIER.MODFRAME MODIFIER)))
	 (subterm (da-access (cdr taf) gterm)))
    (cond ((and (da-literal.is subterm)
		(da-literal.is.equality subterm))
	   (SETQ TAF (DA-TAF.OTHERSIDE TAF))
	   (CAaR (THIRD (ASSOC TAF (GETF (DA-GTERM.ATTRIBUTES GTERM) 'MODFRAMES) :test 'equal)))))))


(DEFUN DA=MODIFIER.PRINT (MODIFIER STREAM DEPTH)

  (DA=MODFRAME.PRINT (DA-MODIFIER.MODFRAME MODIFIER) STREAM DEPTH))



(DEFUN DA=MODFRAME.PRINT (MODFRAME STREAM DEPTH)

  (let (literal)
    (COND ((AND *PRINT-LEVEL* (> DEPTH *PRINT-LEVEL*))
	   (FORMAT STREAM "~A" (DA-modframe.pname modframe)))
	  (t (FORMAT STREAM "~A -> ~A"
		     (COND ((DA-LITERAL.IS (DA-MODFRAME.INPUT MODFRAME))
			    (setq literal (DA-MODFRAME.INPUT MODFRAME))
			    (FORMAT nil "~:[~;Not_~]~A~A"
				    (DA-SIGN.IS.POSITIVE (DA-LITERAL.SIGN LITERAL))
				    (DA-LITERAL.SYMBOL LITERAL)
				    (cond ((DA-LITERAL.TERMLIST LITERAL))
					  (t ""))))
			   (t (DA-MODFRAME.INPUT MODFRAME)))
		     (DA-MODFRAME.VALUE MODFRAME))))))


;;;;;
;;;;;========================================================================================================
;;;;; Chapter 
;;;;; -------
;;;;;
;;;;; Functions to handle the datastructure ATTRIBUTE
;;;;;========================================================================================================


(DEFUN DA-ATTRIBUTE.IS (SEXPR)
  ;;; Input: an sexpression
  ;;; Value: T or NIL, depending whether \verb$SEXPR$ denotes an attribute or not
  
  (EQ (TYPE-OF SEXPR) 'ATTRIBUTE))


(DEFUN DA=ATTRIBUTE.PATTERN.FITS.TERM (PATTERN TERM &OPTIONAL SUBST)
  (LET (ENTRY)
       (COND ((NUMBERP PATTERN)
	      (COND ((SETQ ENTRY (CASSOC PATTERN SUBST))
		     (COND ((EQ ENTRY (DA-TERM.SYMBOL TERM)) SUBST)
			   (T 'FAIL)))
		    ((AND (DA-VARIABLE.IS (DA-TERM.SYMBOL TERM))
			  (EVERY #'(LAMBDA (PAIR) (NEQ (DA-TERM.SYMBOL TERM) (CDR PAIR))) SUBST))
		     (ACONS PATTERN (DA-TERM.SYMBOL TERM) SUBST))
		    (T 'FAIL)))
	     ((ATOM PATTERN)
	      (COND ((SETQ ENTRY (CASSOC PATTERN SUBST))
		     (COND ((EQ ENTRY (DA-TERM.SYMBOL TERM)) SUBST)
			   (T 'FAIL)))
		    ((AND (DA-FUNCTION.IS (DA-TERM.SYMBOL TERM))
			  (EVERY #'(LAMBDA (PAIR) (NEQ (DA-TERM.SYMBOL TERM) (CDR PAIR))) SUBST))
		     (ACONS PATTERN (DA-TERM.SYMBOL TERM) SUBST))
		    (T 'FAIL)))
	     ((AND (EQL (LENGTH (DA-TERM.TERMLIST TERM)) (1- (LENGTH PATTERN)))
		   (NEQ 'FAIL (SETQ SUBST (DA=ATTRIBUTE.PATTERN.FITS.TERM (CAR PATTERN) TERM SUBST)))
		   (EVERY #'(LAMBDA (SUB.PATTERN SUB.TERM)
				    (SETQ SUBST (DA=ATTRIBUTE.PATTERN.FITS.TERM SUB.PATTERN SUB.TERM SUBST))
				    (NEQ SUBST 'FAIL))
			  (CDR PATTERN) (DA-TERM.TERMLIST TERM)))
	      SUBST)
	     (T 'FAIL))))


(DEFUN DA=ATTRIBUTE.FCT.COMMUTATIVE (LITERAL SIDE)
  
  ;;; Input :  two terms
  ;;; Effect:  checks whether left=right is a instance of the commutativity law $f(x y) = f(y x)$
  ;;; Value :  if so, a list \verb$(commutative f (x y))$ is returned
  
  (LET ((SUBST (DA=ATTRIBUTE.PATTERN.FITS.TERM '(F 1 2) (DA-ACCESS SIDE LITERAL))))
       (COND ((NEQ 'FAIL SUBST)
	      (SETQ SUBST (DA=ATTRIBUTE.PATTERN.FITS.TERM '(F 2 1) (DA-ACCESS (DA-TAF.OTHERSIDE SIDE) LITERAL) SUBST))
	      (COND ((NEQ 'FAIL SUBST)
		     (VALUES (CASSOC 'F SUBST) 
			     (DA=ATTRIBUTE.CREATE 'COMMUTATIVE NIL LITERAL (FORMAT NIL "~A is commutative" (CASSOC 'F SUBST))))))))))


(DEFUN DA=ATTRIBUTE.FCT.ASSOCIATIVE (LITERAL SIDE)
  
  ;;; Input :  two terms
  ;;; Effect:  checks whether left=right is a instance of the associativity law $f(f(x y) z) = f(x f(y z))$
  ;;; Value:   if so, a list \verb$(associative f (x y z))$ is returned
  
  (LET ((SUBST (DA=ATTRIBUTE.PATTERN.FITS.TERM '(F (F 1 2) 3) (DA-ACCESS SIDE LITERAL))))
       (COND ((NEQ 'FAIL SUBST)
	      (SETQ SUBST (DA=ATTRIBUTE.PATTERN.FITS.TERM '(F 1 (F 2 3)) (DA-ACCESS (DA-TAF.OTHERSIDE SIDE) LITERAL) SUBST))
	      (COND ((NEQ 'FAIL SUBST)
		     (VALUES (CASSOC 'F SUBST)
			     (DA=ATTRIBUTE.CREATE 'ASSOCIATIVE NIL LITERAL  (FORMAT NIL "~A is associative" (CASSOC 'F SUBST))))))))))


(DEFUN DA=ATTRIBUTE.FCT.NULL.OR.IDENTITY (LITERAL SIDE)
  
  ;;; Input :  two terms
  ;;; Effect:  checks whether left=right describe a null-element e.g. $f(x e) = e or f(e x) = e$
  ;;; Value:   if so, a list \verb$(null f e position (e x))$ is returned
  
  (LET ((LEFT (DA-ACCESS SIDE LITERAL)) (RIGHT (DA-ACCESS (DA-TAF.OTHERSIDE SIDE) LITERAL))
	USED.VARIABLES CONSTANT POSITION ID.POSITION SYMBOL)
       (COND ((AND (EQL 2 (LENGTH (DA-TERM.TERMLIST LEFT)))
		   (NULL (DA-TERM.TERMLIST RIGHT))
		   (SETQ POSITION (POSITION RIGHT (DA-TERM.TERMLIST LEFT) :TEST 'UNI-TERM.ARE.EQUAL))
		   (EVERY #'(LAMBDA (TERM SORT)
				    (SETQ SYMBOL (DA-TERM.SYMBOL TERM))
				    (COND ((AND (DA-VARIABLE.IS SYMBOL)
						(NOT (MEMBER SYMBOL USED.VARIABLES))
						(EQ (DA-VARIABLE.SORT SYMBOL) SORT))
					   (PUSH SYMBOL USED.VARIABLES))
					  ((AND (NULL CONSTANT)
						(NULL (DA-TERM.TERMLIST TERM))
						(DA-FUNCTION.IS SYMBOL))
					   (SETQ CONSTANT SYMBOL))))
			  (DA-TERM.TERMLIST LEFT) (DA-FUNCTION.DOMAIN.SORTS (DA-TERM.SYMBOL LEFT))))
	      (SETQ POSITION (LIST (INCF POSITION)))
	      (SETQ ID.POSITION (DA-TAF.OTHERSIDE POSITION))
	      (VALUES (DA-TERM.SYMBOL LEFT) 
		      (COND ((EQL CONSTANT (DA-TERM.SYMBOL RIGHT))
			     (DA=ATTRIBUTE.CREATE 'NULL (LIST CONSTANT POSITION SIDE) LITERAL
						  (FORMAT NIL "~A is a null element for the ~D.position of ~A" 
							  CONSTANT (car POSITION) (DA-TERM.SYMBOL LEFT))))
			    ((DA-VARIABLE.IS (DA-TERM.SYMBOL RIGHT))
			     (DA=ATTRIBUTE.CREATE 'IDENTITY (LIST CONSTANT ID.POSITION SIDE) LITERAL
						  (FORMAT NIL "~A is a identity for the ~D.position of ~A" 
							  CONSTANT (car ID.POSITION) (DA-TERM.SYMBOL LEFT))))))))))

(DEFUN DA=ATTRIBUTE.FCT.INVERSE (LITERAL SIDE)
  
  ;;; Input:   an equation and a taf
  ;;; Effect:  checks whether LITERAL is an equation like $f(x_1 ... g(y_1 ... y_n) ... x_n) = y_i$
  ;;;          and $x_1,...,x_n$ is a subset of $\{ y_1,..., y_(i-1), y_(i+1),..., y_n \}$
  
  (LET ((LEFT (DA-ACCESS SIDE LITERAL)) (RIGHT (DA-ACCESS (DA-TAF.OTHERSIDE SIDE) LITERAL))
	OK OTHER.VARS POSITION USED.VARS)
       (COND ((NUMBERP (MULTIPLE-VALUE-SETQ (POSITION USED.VARS)
					    (DA-TERM.IS.MOST.GENERAL LEFT T)))
	      (MULTIPLE-VALUE-SETQ (OK OTHER.VARS)
					  (DA-TERM.IS.MOST.GENERAL (NTH (1- POSITION) (DA-TERM.TERMLIST LEFT))))
	      (COND (ok (COND ((AND (MEMBER (DA-TERM.SYMBOL RIGHT) OTHER.VARS)
				    (NOT (MEMBER (DA-TERM.SYMBOL RIGHT) USED.VARS))
				    (SUBSETP USED.VARS OTHER.VARS))
			       (VALUES (DA-TERM.SYMBOL (NTH (1- POSITION) (DA-TERM.TERMLIST LEFT)))
				       (DA=ATTRIBUTE.CREATE 'INVERSE (LIST POSITION SIDE) LITERAL
							    (FORMAT NIL "~A is the inverse for ~A in the ~A. argument"
								    (DA-TERM.SYMBOL LEFT)
								    (DA-TERM.SYMBOL (NTH (1- POSITION)
											 (DA-TERM.TERMLIST LEFT)))
								    POSITION)))))))))))


(DEFUN DA=ATTRIBUTE.PRED.REFLEXIVE (LITERALS)
  (COND ((AND (EQL 1 (LENGTH LITERALS))
	      (DA-SIGN.IS.POSITIVE (DA-LITERAL.SIGN (CAR LITERALS)))
	      (EQL 2 (DA-PREDICATE.ARITY (DA-GTERM.SYMBOL (CAR LITERALS))))
	      (UNI-TERM.ARE.EQUAL (CAR (DA-GTERM.TERMLIST (CAR LITERALS)))
				  (SECOND (DA-GTERM.TERMLIST (CAR LITERALS)))))
	 (VALUES (DA-GTERM.SYMBOL (CAR LITERALS)) 
		 (DA=ATTRIBUTE.CREATE 'REFLEXIVE NIL (CAR LITERALS)
				      (FORMAT NIL "~A is reflexive" (DA-GTERM.SYMBOL (CAR LITERALS))))))))


(DEFUN DA=ATTRIBUTE.PRED.IRREFLEXIVE (LITERALS)
  (COND ((AND (EQL 1 (LENGTH LITERALS))
	      (DA-SIGN.IS.NEGATIVE (DA-LITERAL.SIGN (CAR LITERALS)))
	      (EQL 2 (DA-PREDICATE.ARITY (DA-GTERM.SYMBOL (CAR LITERALS))))
	      (UNI-TERM.ARE.EQUAL (CAR (DA-GTERM.TERMLIST (CAR LITERALS)))
				  (SECOND (DA-GTERM.TERMLIST (CAR LITERALS)))))
	 (VALUES (DA-GTERM.SYMBOL (CAR LITERALS)) 
		 (DA=ATTRIBUTE.CREATE 'IRREFLEXIVE NIL (CAR LITERALS)
				      (FORMAT NIL "~A is irreflexive" (DA-GTERM.SYMBOL (CAR LITERALS))))))))


(DEFUN DA=ATTRIBUTE.PRED.SYMMETRIC (LITERALS)
  (COND ((AND (EQL 2 (LENGTH LITERALS))
	      (NEQ (DA-LITERAL.SIGN (CAR LITERALS)) (DA-LITERAL.SIGN (SECOND LITERALS)))
	      (EQ (DA-GTERM.SYMBOL (CAR LITERALS)) (DA-GTERM.SYMBOL (SECOND LITERALS)))
	      (EQL 2 (DA-PREDICATE.ARITY (DA-GTERM.SYMBOL (CAR LITERALS))))
	      (EVERY #'(LAMBDA (X) (DA-VARIABLE.IS (DA-GTERM.SYMBOL X))) (DA-GTERM.TERMLIST (CAR LITERALS)))
	      (UNI-TERMLIST.ARE.EQUAL (DA-GTERM.TERMLIST (CAR LITERALS)) (REVERSE (DA-GTERM.TERMLIST (SECOND LITERALS)))))
	 (VALUES (DA-GTERM.SYMBOL (CAR LITERALS)) 
		 (DA=ATTRIBUTE.CREATE 'SYMMETRIC NIL LITERALS
				      (FORMAT NIL "~A is symmetric" (DA-GTERM.SYMBOL (CAR LITERALS))))))))


(DEFUN DA=ATTRIBUTE.PRED.TRANSITIVE (LITERALS)
  (LET (POS.LIT)
       (COND ((AND (EQL 3 (LENGTH LITERALS))
		   (EQ (DA-GTERM.SYMBOL (CAR LITERALS)) (DA-GTERM.SYMBOL (SECOND LITERALS)))
		   (EQ (DA-GTERM.SYMBOL (CAR LITERALS)) (DA-GTERM.SYMBOL (THIRD LITERALS)))
		   (EQL 1 (COUNT-IF #'(LAMBDA (LIT) 
					      (COND ((DA-SIGN.IS.POSITIVE (DA-LITERAL.SIGN LIT))
						     (SETQ POS.LIT LIT))))
				    LITERALS)))
	      (COND ((SOME #'(LAMBDA (LIT1)
				     (AND (DA-SIGN.IS.NEGATIVE (DA-LITERAL.SIGN LIT1))
					  (UNI-TERM.ARE.EQUAL (CAR (DA-GTERM.TERMLIST LIT1)) (CAR (DA-GTERM.TERMLIST POS.LIT)))
					  (SOME #'(LAMBDA (LIT2)
							  (COND ((AND (DA-SIGN.IS.NEGATIVE (DA-LITERAL.SIGN LIT2))
								      (UNI-TERM.ARE.EQUAL (SECOND (DA-GTERM.TERMLIST LIT1)) 
											  (CAR (DA-GTERM.TERMLIST LIT2)))
								      (UNI-TERM.ARE.EQUAL (SECOND (DA-GTERM.TERMLIST LIT2)) 
											  (SECOND (DA-GTERM.TERMLIST POS.LIT))))
								 LIT2)))
						LITERALS)))
			   LITERALS)
		     (VALUES (DA-GTERM.SYMBOL (CAR LITERALS))
			     (DA=ATTRIBUTE.CREATE 'TRANSITIVE NIL LITERALS
						  (FORMAT NIL "~A is transitive" (DA-GTERM.SYMBOL (CAR LITERALS)))))))))))



(DEFUN DA=ATTRIBUTE.CREATE (NAME ARGUMENTS JUSTIFICATION COMMENT &OPTIONAL CONDITIONS)
  (MAKE-ATTRIBUTE :NAME NAME
		  :ARGUMENTS ARGUMENTS
		  :JUSTIFICATION JUSTIFICATION
		  :COMMENT COMMENT
		  :CONDITIONS CONDITIONS))





;;; diversa

(DEFMACRO DA-TYPE (OBJECT)
  
  ;;; Value:  the lisp-type of this object.
  
  `(type-of ,OBJECT))


(DEFUN DA-PNAME (OBJECT)
  
  ;;; Input:  a lisp-object
  ;;; Value:  same expression, where all objects are replaced by their printed representation.

  (CASE (TYPE-OF OBJECT)
    (GTERM (DA-GTERM.PNAME OBJECT))
    (LITERAL (DA-LITERAL.PNAME OBJECT))
    ((DA*VARIABLE DA*PREDICATE DA*FUNCTION) (DA-SYMBOL.PNAME OBJECT))
    (DA*SORT (DA-SORT.PNAME OBJECT))
    (OTHERWISE OBJECT)))


;;;;;
;;;;;**********************************************************************************************************
;;;;;
;;;;;  D A T A B A S E
;;;;;  =========================
;;;;;
;;;;;**********************************************************************************************************


(DEFVAR DB*HISTORY 'DED-INPUT.HISTORY)

(DEFVAR DB*SORT.ALL NIL)

(DEFVAR DB*FUNCTION.ALL NIL)

(DEFVAR DB*PREDICATE.ALL NIL)

(DEFVAR DB*NAME.ALL (MAKE-HASH-TABLE :TEST #'EQUAL))

(DEFVAR DB*THEOREMS NIL)



;;;;;
;;;;;========================================================================================================
;;;;; Chapter 1
;;;;; ---------
;;;;;
;;;;; Initializing the database-module
;;;;;========================================================================================================



(DEFUN DB-RESET ()

  ;;; Edited: 1-feb-82 13:54:40                        
  ;;; Value:  undefined                                
  ;;; Effect: deletes all variable, constant, function and predicate symbols and sets the system
  ;;;         to an initial state.

  (SETQ DB*SORT.ALL NIL)
  (SETQ DB*FUNCTION.ALL NIL)
  (SETQ DB*PREDICATE.ALL NIL)
  (CLRHASH DB*NAME.ALL))


;;;;;
;;;;;========================================================================================================
;;;;; Chapter 2
;;;;; ---------
;;;;;
;;;;; Maintaining the insertion and deletion of sorts, functions or predicates
;;;;;========================================================================================================


(DEFUN DB-NAME.OBJECT (NAME)

  ;;; Input:  a string
  ;;; Value:  the datastructure objects named by \verb$NAME$
  
  (GETHASH (STRING-DOWNCASE NAME) DB*NAME.ALL))


(DEFUN DB-NAME.SORT (NAME)
  ;;; edited : 15.03.93 by CS
  ;;; input  : a string
  ;;; value  : the sort object of the database with name \verb$NAME$ if such an object exists, else NIL

  (FIND-IF #'DA-SORT.IS (DB-NAME.OBJECT NAME)))


(DEFUN DB-NAME.FUNCTION (NAME DOMAIN RANGE)
  ;;; edited : 15.03.93 by CS
  ;;; input  : a string denoting a function, its domain sorts and its range sort
  ;;; value  : the function of the database with name \verb$NAME$, with domain \verb$DOMAIN$,
  ;;;          and with range \verb$RANGE$,
  ;;;          if such an object exists, else NIL

  (FIND-IF #'(LAMBDA (OBJECT)
	       (AND (DA-FUNCTION.IS OBJECT)
		    (EQ RANGE (DA-FUNCTION.SORT OBJECT))
		    (EQUAL DOMAIN (DA-FUNCTION.DOMAIN.SORTS OBJECT))))
	   (DB-NAME.OBJECT NAME)))


(DEFUN DB-NAME.PREDICATE (NAME DOMAIN)
  ;;; edited : 15.03.93 by CS
  ;;; input  : a string denoting a predicate and its domain sorts
  ;;; value  : the predicate of the database with name \verb$NAME$ and with domain \verb$DOMAIN$
  ;;;          if such an object exists, else NIL

  (FIND-IF #'(LAMBDA (OBJECT)
	       (AND (DA-PREDICATE.IS OBJECT)
		    (EQUAL DOMAIN (DA-PREDICATE.DOMAIN.SORTS OBJECT))))
	   (DB-NAME.OBJECT NAME)))


(DEFUN DB=NAME.INSERT (NAME OBJECT)

  (PUSH OBJECT (GETHASH (STRING-DOWNCASE NAME) DB*NAME.ALL)))


(DEFUN DB=NAME.DELETE (NAME OBJECT)

  (SETQ NAME (STRING-DOWNCASE NAME))
  (SETF (GETHASH NAME DB*NAME.ALL)
	(DELETE OBJECT (GETHASH NAME DB*NAME.ALL))))


(DEFMACRO DB-SORT.ALL ()

  ;;; Value:  a list of all sorts in the database.
                        
 `DB*SORT.ALL)


(DEFUN DB-SORT.INSERT (SORT)
  
  ;;; Edited: 11-feb-83 09:38:54                           
  ;;; Input:  a string and a list of sorts               
  ;;; Effect: a sort with name \verb$NAME$ is created with direct subsorts \verb$DIRECT.SUBSORTS$ and added to the database
  ;;; Value:  the generated sort.
  
  (DB=SORT.UPDATE.OTHER.SORTS SORT (DA-SORT.DIRECT.SUBSORTS SORT))
  (DB=NAME.INSERT (DA-SORT.PNAME SORT) SORT)
  (PUSH SORT DB*SORT.ALL)
  (SETF (DA-SORT.DEFINING.INPUT SORT) (DED-INPUT.ACTUAL.INPUT))
  (DED-INPUT.HISTORY.INSERT `(DB-SORT.DELETE ,SORT)))


(DEFUN DB-SORT.UPDATE.SORT (NEW.SORT SUBSORTS ATTRIBUTES)
  
  ;;; Edited: 22-feb-89 mp                          
  ;;; Input:  a sort, its direct subsorts (not the transitive closure) and a list of attributes.
  ;;; Effect: \verb$SORT$ is inserted into the database, the \verb$SUBSORTS$ are inserted into        
  ;;;         the corresponding slots of sort and the attribute-slot is updated.   
  ;;; Value:  the sort itself
  
  (SETF (DA-SORT.DIRECT.SUBSORTS NEW.SORT) SUBSORTS)
  (SETF (DA-SORT.DIRECT.SUPERSORTS NEW.SORT) (LIST (DP-SORT.TOP.LEVEL.SORT)))
  (SETF (DA-SORT.ATTRIBUTES NEW.SORT) ATTRIBUTES)
  (DB=SORT.UPDATE.OTHER.SORTS NEW.SORT SUBSORTS))


(DEFUN DB=SORT.UPDATE.OTHER.SORTS (NEW.SORT SUBSORTS)

  ;;; Edited: 11-FEB-83 09:38:54                           
  ;;; Input:  a sort and its direct subsorts (not the transitive closure)
  ;;; Effect: all.subsorts and all.supersorts of \verb$NEW.SORT$ are updated.       
  ;;; Value:  the sort itself
  
  (LET (ALL.SUBSORTS)
    (SETF (DA-SORT.ALL.SUPERSORTS NEW.SORT)
	  (LIST NEW.SORT (DP-SORT.TOP.LEVEL.SORT)))
    (PUSH NEW.SORT (DA-SORT.ALL.SUBSORTS (DP-SORT.TOP.LEVEL.SORT)))
    (PUSH NEW.SORT (DA-SORT.DIRECT.SUBSORTS (DP-SORT.TOP.LEVEL.SORT)))
    (MAPC #'(LAMBDA (SORT)
	      (SETF (DA-SORT.DIRECT.SUPERSORTS SORT)
		    (CONS NEW.SORT (DELETE (DP-SORT.TOP.LEVEL.SORT) (DA-SORT.DIRECT.SUPERSORTS SORT))))
	      (SETF (DA-SORT.DIRECT.SUBSORTS (DP-SORT.TOP.LEVEL.SORT))
		    (DELETE SORT (DA-SORT.DIRECT.SUBSORTS (DP-SORT.TOP.LEVEL.SORT))))
	      (PUSH NEW.SORT (DA-SORT.ALL.SUPERSORTS SORT))
	      (SETQ ALL.SUBSORTS (UNION (COPY-LIST (DA-SORT.ALL.SUBSORTS SORT)) ALL.SUBSORTS)))
	  SUBSORTS)
    (MAPC #'(LAMBDA (SORT)
	      (PUSH NEW.SORT (DA-SORT.ALL.SUPERSORTS SORT)))
	  ALL.SUBSORTS)
    (SETF (DA-SORT.ALL.SUBSORTS NEW.SORT) (CONS NEW.SORT ALL.SUBSORTS))
    NEW.SORT))


(DEFUN DB-SORT.DELETE (SORT)

  ;;; Input:   a sort
  ;;; Effect:  removes \verb$SORT$ from the database and updates the entries of other sorts.
  ;;; Value:   undefined.

  (DB=NAME.DELETE (DA-SORT.PNAME SORT) SORT)
  (SETQ DB*SORT.ALL (DELETE SORT DB*SORT.ALL))
  (MAPC #'(LAMBDA (SUBSORT)
	    (SETF (DA-SORT.DIRECT.SUPERSORTS SUBSORT) 
		  (COND ((DELETE SORT (DA-SORT.DIRECT.SUPERSORTS SUBSORT)))
			(T (LIST (DP-SORT.TOP.LEVEL.SORT))))))
	(DA-SORT.DIRECT.SUBSORTS SORT))
  (MAPC #'(LAMBDA (SUPERSORT)
	    (SETF (DA-SORT.DIRECT.SUBSORTS SUPERSORT) 
		  (DELETE SORT (DA-SORT.DIRECT.SUBSORTS SUPERSORT))))
	(DA-SORT.DIRECT.SUPERSORTS SORT))
  (MAPC #'(LAMBDA (SUBSORT)
	    (SETF (DA-SORT.ALL.SUPERSORTS SUBSORT) 
		  (COND ((DELETE SORT (DA-SORT.ALL.SUPERSORTS SUBSORT)))
			(T (LIST (DP-SORT.TOP.LEVEL.SORT))))))
	(DA-SORT.ALL.SUBSORTS SORT))
  (MAPC #'(LAMBDA (SUPERSORT)
	    (SETF (DA-SORT.ALL.SUBSORTS SUPERSORT) 
		  (DELETE SORT (DA-SORT.ALL.SUBSORTS SUPERSORT))))
	(DA-SORT.ALL.SUPERSORTS SORT)))



(DEFUN DB-SYMBOL.ATTRIBUTE.INSERT (SYMBOL INDICATOR VALUE)

  ;;; Input:   a symbol, an indicator and its value
  ;;; Effect:  changes the \verb$INDICATOR$ slot of the attributes of \verb$SYMBOL$ to value and
  ;;;          saves its current value on the history stack.
  ;;; Value:   undefined
  
  (DED-INPUT.HISTORY.INSERT `(DB-SYMBOL.ATTRIBUTE.INSERT (QUOTE ,SYMBOL) (QUOTE ,INDICATOR)
							 (QUOTE ,(GETF (DA-SYMBOL.ATTRIBUTES SYMBOL) INDICATOR))))
  (DA-SYMBOL.ATTRIBUTE.INSERT SYMBOL INDICATOR VALUE))


(DEFUN DB-SYMBOL.ATTRIBUTE.DELETE (SYMBOL INDICATOR)

  ;;; Input:   a symbol and  an indicator
  ;;; Effect:  remove the attribute denoted by \verb$INDICATOR$ and saves its previous a on the history stack
  ;;;          of \verb$SYMBOL$.
  ;;; Value:   undefined.

  (DED-INPUT.HISTORY.INSERT `(DB-SYMBOL.ATTRIBUTE.INSERT (QUOTE ,SYMBOL) (QUOTE ,INDICATOR)
					   (QUOTE ,(GETF (DA-SYMBOL.ATTRIBUTES SYMBOL) INDICATOR))))
  (DA-SYMBOL.ATTRIBUTE.DELETE SYMBOL INDICATOR))



(DEFUN DB-FUNCTION.INSERT (FUNCTION)

  ;;; Input:   a function (see DA)
  ;;; Effect:  inserts function into the database
  ;;; Value:   the inserted function

  (DED-INPUT.HISTORY.INSERT `(DB-FUNCTION.DELETE (QUOTE ,FUNCTION)))
  (SETF (DA-FUNCTION.DEFINING.INPUT FUNCTION) (DED-INPUT.ACTUAL.INPUT))
  (setf (getf (da-function.attributes function) 'expand.stack) (DED-INPUT.FILE.STACK))
  (SETQ DB*FUNCTION.ALL (MERGE 'LIST (LIST FUNCTION) DB*FUNCTION.ALL #'STRING-LESSP
			       :KEY #'(LAMBDA (X) (DA-PREFUN.PNAME X))))
  (DB=NAME.INSERT (DA-FUNCTION.PNAME FUNCTION) FUNCTION)
  FUNCTION)


(DEFUN DB-FUNCTION.DELETE (FUNCTION)

  ;;; Input:   a function (see DA)
  ;;; Effect:  removes function from the database.
  ;;; Value:   undefined.

  (SETQ DB*FUNCTION.ALL (DELETE FUNCTION DB*FUNCTION.ALL :COUNT 1))
  (DB=NAME.DELETE (DA-FUNCTION.PNAME FUNCTION) FUNCTION))


(DEFUN DB-FUNCTION.ALL ()

  ;;; Value:  a list of all functions in the database.
                        
 (REMOVE-IF-NOT #'(LAMBDA (FUNC) (DED-INPUT.IS.ACTIVE (DA-OBJECT.DEFINING.INPUT FUNC)))
		DB*FUNCTION.ALL))


(DEFUN DB-PREDICATE.INSERT (PREDICATE)

  ;;; Input:   a predicate (see DA)
  ;;; Effect:  inserts predicate into the database
  ;;; Value:   the inserted predicate.

  (DED-INPUT.HISTORY.INSERT `(DB-PREDICATE.DELETE (QUOTE ,PREDICATE)))
  (SETF (DA-PREDICATE.DEFINING.INPUT PREDICATE) (DED-INPUT.ACTUAL.INPUT))
  (setf (getf (da-predicate.attributes predicate) 'expand.stack) (DED-INPUT.FILE.STACK))
  (DB=NAME.INSERT (DA-PREDICATE.PNAME PREDICATE) PREDICATE)
  (SETQ DB*PREDICATE.ALL (MERGE 'LIST (LIST PREDICATE) DB*PREDICATE.ALL #'STRING-LESSP
				:KEY #'(LAMBDA (X) (DA-PREFUN.PNAME X))))
  PREDICATE)


(DEFUN DB-PREDICATE.DELETE (PREDICATE)

  ;;; Input:   a predicate (see DA)
  ;;; Effect:  removes predicate from the database.
  ;;; Value:   undefined.

  (SETQ DB*PREDICATE.ALL (DELETE PREDICATE DB*PREDICATE.ALL :COUNT 1))
  (DB=NAME.DELETE (DA-PREDICATE.PNAME PREDICATE) PREDICATE))


(DEFUN DB-PREDICATE.ALL ()

  ;;; Value:  a list of all functions in the database.
                       
  (REMOVE-IF-NOT #'(LAMBDA (PRED) (DED-INPUT.IS.ACTIVE (DA-OBJECT.DEFINING.INPUT PRED)))
		 DB*PREDICATE.ALL))


(DEFUN DB-PREFUN.FORMULAS.ALL (PREFUN)

  ;;; Input:  a prefun
  ;;; Value:  list of all formulas, in which prefun occurs.
  
  (COND ((DA-FUNCTION.IS PREFUN)
	 (DB-PREFUN.MODIFIER.ALL PREFUN))
	((AND (DA-PREDICATE.IS PREFUN)
	      (NOT (DA-PREDICATE.IS.EQUALITY PREFUN)))
	 (REMOVE-DUPLICATES
	  (MAPCAN #'(LAMBDA (TYPE)
		      (MAPCAN #'(LAMBDA (FORMULA)
				  (cond ((ded-input.is.active (da-gterm.defining.input (car formula)))
					 (list (third (cdr formula))))))
			      (GETF (DA-PREFUN.DATABASE PREFUN) TYPE)))
		  '(++ + -- -))))))


(DEFUN DB-PREFUN.MODIFIER.ALL (PREFUN)
  
  ;;; Input:  a prefun
  ;;; Value:  list of modifiers, which denote all possible deductions based on prefun.
  ;;; Notice: to be changed, in case of predicates no sign of literal is considered.
 
  (REMOVE-IF-NOT #'(LAMBDA (MODIFIER)
		     (ded-input.is.active (da-modifier.defining.input MODIFIER)))
		 (APPEND (GETF (DA-PREFUN.MODIFIERS PREFUN) 'CHANGING)
			 (GETF (DA-PREFUN.MODIFIERS PREFUN) 'TOP.LEVEL))))


(DEFUN DB-PREDICATE.DATABASE.SELECTION (GTERM SIGN BODY)

  ;;; Input:  a gterm, an atom, a sign and a functional
  ;;; Effect: searches the first modifier of type \verb$TYPE$ for the prefun of \verb$GTERM$
  ;;;         which satisfies \verb$BODY$
  ;;; Value:  the result of applying the modifier to \verb$BODY$
  
  (COND ((DA-PREDICATE.IS.EQUALITY (DA-GTERM.SYMBOL GTERM))
	 (SOME #'(LAMBDA (SORT)
		   (SOME #'(LAMBDA (ENTRY)
			     (COND ((ded-input.is.active (da-gterm.defining.input (car entry)))
				    (FUNCALL BODY (cdr ENTRY)))))
			 (GETF (GETF (DA-PREFUN.DATABASE (DA-PREDICATE.EQUALITY)) SIGN) SORT)))
	       (DA-SORT.ALL.SUBSORTS (DA-TERM.SORT (CAR (DA-GTERM.TERMLIST GTERM))))))
	(T (SOME #'(LAMBDA (ENTRY)
		     (COND ((ded-input.is.active (da-gterm.defining.input (car entry)))
			    (FUNCALL BODY (cdr ENTRY)))))
		 (GETF (DA-PREFUN.DATABASE (DA-GTERM.SYMBOL GTERM)) SIGN)))))


(DEFUN DB-PREDICATE.DATABASE.COLLECTION (GTERM SIGN BODY)

  ;;; Input:  a gterm, an atom, a sign and a functional
  ;;; Effect: searches for all modifiers of type \verb$TYPE$ for the prefun of \verb$GTERM$
  ;;;         which satisfy \v rb$BODY$
  ;;; Value:  the concatenation of all results of applying the modifiers to \verb$BODY$
  
  (COND ((DA-PREDICATE.IS.EQUALITY (DA-GTERM.SYMBOL GTERM))
	  (MAPCAN #'(LAMBDA (SORT)
		    (MAPCAN #'(LAMBDA (ENTRY)
				(COND ((ded-input.is.active (da-gterm.defining.input (car entry)))
				       (FUNCALL BODY (cdr ENTRY)))))
			    (GETF (GETF (DA-PREFUN.DATABASE (DA-PREDICATE.EQUALITY)) SIGN) SORT)))
		(DA-SORT.ALL.SUBSORTS (DA-TERM.SORT (CAR (DA-GTERM.TERMLIST GTERM))))))
	 (T (MAPCAN #'(LAMBDA (ENTRY)
			 (COND ((ded-input.is.active (da-gterm.defining.input (car entry)))
				(FUNCALL BODY (cdr ENTRY)))))
		    (GETF (DA-PREFUN.DATABASE (DA-GTERM.SYMBOL GTERM)) SIGN)))))


(DEFUN DB-FUNCTION.DATABASE.COLLECTION (GTERM SIGN BODY)

  ;;; Input:  a gterm, an atom, a sign and a functional
  ;;; Effect: searches for all modifiers of type \verb$TYPE$ for the prefun of \verb$GTERM$
  ;;;         which satisfy \v rb$BODY$
  ;;; Value:  the concatenation of all results of applying the modifiers to \verb$BODY$
  
  (MAPCAN #'(LAMBDA (ENTRY)
	      (COND ((ded-input.is.active (da-gterm.defining.input (car entry)))
		     (FUNCALL BODY (cdr ENTRY)))))
	  (GETF (DA-PREFUN.DATABASE (DA-GTERM.SYMBOL GTERM)) SIGN)))
	 
	 
(DEFUN DB=PREFUN.DATABASE.ADD (PREFUN INDICATOR VALUE &OPTIONAL SORT.FCT GTERM)

  ;;; Input:   a function/predicate symbol, an atom, an sexpression and a sort-function and the
  ;;;          top-level gterm generating this entry
  ;;; Effect:  inserts \verb$VALUE$ under the given \verb$INDICATOR$ into the database of
  ;;;          \verb$PREFUN$ and updates the history-slot of \verb$GTERM$
  ;;; Value:   undefined

  (LET ((SORT (COND ((and (DA-PREDICATE.IS PREFUN) (DA-PREDICATE.IS.EQUALITY prefun))
		     (DA-symbol.SORT (DA-GTERM.SYMBOL (CAR (DA-GTERM.TERMLIST (CAR VALUE)))))))))
    (SETQ VALUE (CONS GTERM VALUE))
    (COND ((and (DA-PREDICATE.IS PREFUN)
		(DA-PREDICATE.IS.EQUALITY prefun))
	   (COND ((NULL SORT.FCT)
		  (PUSH VALUE (GETF (GETF (DA-PREFUN.DATABASE PREFUN) INDICATOR) SORT)))
		 (T (SETF (GETF (GETF (DA-PREFUN.DATABASE PREFUN) INDICATOR) SORT)
			  (MERGE 'LIST (LIST VALUE)
				 (GETF (GETF (DA-PREFUN.DATABASE PREFUN) INDICATOR) SORT)
				 SORT.FCT)))))
	  (T (COND ((NULL SORT.FCT)
		    (PUSH VALUE (GETF (DA-PREFUN.DATABASE PREFUN) INDICATOR)))
		   (T (SETF (GETF (DA-PREFUN.DATABASE PREFUN) INDICATOR)
			    (MERGE 'LIST (LIST VALUE)
				   (GETF (DA-PREFUN.DATABASE PREFUN) INDICATOR)
				   SORT.FCT))))))
    (COND (GTERM (PUSH #'(LAMBDA () (DB=PREFUN.DATABASE.REMOVE PREFUN INDICATOR VALUE))
		       (GETF (DA-GTERM.ATTRIBUTES GTERM) 'HISTORY))))))


(DEFUN DB=PREFUN.DATABASE.REMOVE (PREFUN INDICATOR VALUE)

  (LET ((SORT (COND ((and (DA-PREDICATE.IS PREFUN) (DA-PREDICATE.IS.EQUALITY prefun))
		     (DA-symbol.SORT (DA-GTERM.SYMBOL (CAR (DA-GTERM.TERMLIST (CAR (CDR VALUE))))))))))
    (COND ((and (DA-PREDICATE.IS PREFUN)
		(DA-PREDICATE.IS.EQUALITY prefun))
	   (SETF (GETF (GETF (DA-PREFUN.DATABASE PREFUN) INDICATOR) SORT)
		 (DELETE VALUE (GETF (GETF (DA-PREFUN.DATABASE PREFUN) INDICATOR) SORT) :COUNT 1)))
	  (T (SETF (GETF (DA-PREFUN.DATABASE PREFUN) INDICATOR)
		   (DELETE VALUE (GETF (DA-PREFUN.DATABASE PREFUN) INDICATOR) :COUNT 1))))))


;;;;;
;;;;;========================================================================================================
;;;;; Chapter 3
;;;;; ---------
;;;;;
;;;;; Functions to insert formulas and definitions into the database.
;;;;;========================================================================================================


(DEFUN DB-FORMULA.INSERT (FORMULA NAME &optional TYPE)
  
  ;;; Input:   a prefix-formula and an atom \verb$AXIOM$ or \verb$LEMMA$
  ;;; Effect:  the formula is inserted into the database with \verb$NAME$.
  ;;; Value:   List of all gterms representing \verb$FORMULA$

  (COND ((EQ TYPE 'AXIOM) (DB=EQUIVALENCE.DEFINING.SYMBOLS FORMULA)))
  (LET ((GTERM (NORM-NORMALIZATION FORMULA)))
    (SETQ GTERM (COND ((EQ 'AND (DA-GTERM.SYMBOL GTERM))
		       (DA-GTERM.TERMLIST GTERM))
		      (T (LIST GTERM))))
    (MAPC #'(LAMBDA (GTERM)
	      (SETF (DA-GTERM.PNAME GTERM) (FORMAT NIL "~A" NAME))
	      (DB-GTERM.INSERT GTERM TYPE))
	  GTERM)
    GTERM))


(DEFUN DB=EQUIVALENCE.DEFINING.SYMBOLS (FORMULA)

  ;;; Input:  a formula
  ;;; Effect: searches for equivalences $(\Phi \leftrightarrow \Psi)$ in \verb$FORMULA$ (with $\Psi$ a literal),
  ;;;         such that each variable in $\Psi$ occurs in $\Phi$ and the termlist of $\Phi$ contains only
  ;;;         variables, constructors 

  (LET ((VARS (DA-GTERM.VARIABLES FORMULA)) TERMLIST EQV.TAFS)
    (SETQ EQV.TAFS (remove-if-not #'(lambda (taf) (da-gterm.taf.is.unnegated formula taf))
				  (DA-SYMBOL.OCCURS.IN.GTERM 'EQV FORMULA)))
    (MAPC #'(LAMBDA (TAF)
	      (SETQ TERMLIST (DA-GTERM.TERMLIST (DA-ACCESS TAF FORMULA)))
	      (COND ((AND (DA-LITERAL.IS (CAR TERMLIST))
			  (DB=GTERM.IS.GENERAL (CAR TERMLIST))
			  (NULL (DA-PREFUN.DEFINITION (DA-GTERM.SYMBOL (CAR TERMLIST))))
			  (NULL (SET-DIFFERENCE VARS (DA-GTERM.VARIABLES (DA-ACCESS TAF FORMULA))))
			  (DB=SYMBOL.INSERT.DEFINING.SYMBOLS (DA-LITERAL.SYMBOL (CAR TERMLIST)) FORMULA)))
		    ((AND (DA-LITERAL.IS (SECOND TERMLIST))
			  (DB=GTERM.IS.GENERAL (SECOND TERMLIST))
			  (NULL (DA-PREFUN.DEFINITION (DA-GTERM.SYMBOL (SECOND TERMLIST))))
			  (NULL (SET-DIFFERENCE VARS (DA-GTERM.VARIABLES (DA-ACCESS TAF FORMULA))))
			  (DB=SYMBOL.INSERT.DEFINING.SYMBOLS (DA-LITERAL.SYMBOL (SECOND TERMLIST)) FORMULA)))))
	  EQV.TAFS)
    (MAPC #'(LAMBDA (TAF)
	      (COND ((NOT (SOME #'(LAMBDA (EQV.TAF) (DA-TAF.IS.SUBTAF EQV.TAF TAF)) EQV.TAFS))
		     (DB=EQUALITY.DEFINING.SYMBOLS VARS (DA-GTERM.TERMLIST (DA-ACCESS TAF FORMULA)) FORMULA))))
	  (DA-SYMBOL.OCCURS.IN.GTERM (DA-PREDICATE.EQUALITY) FORMULA))))



(DEFUN DB=EQUALITY.DEFINING.SYMBOLS (VARS TERMLIST GTERM)

  (LET ((LEFT.VARS (DA-GTERM.VARIABLES (CAR TERMLIST)))
	(RIGHT.VARS (DA-GTERM.VARIABLES (SECOND TERMLIST))))
    (COND ((AND (DB=GTERM.IS.GENERAL (CAR TERMLIST))
		(NULL (SET-DIFFERENCE VARS LEFT.VARS))
		(NULL (DA-PREFUN.DEFINITION (DA-GTERM.SYMBOL (CAR TERMLIST))))
		(DB=SYMBOL.INSERT.DEFINING.SYMBOLS (DA-GTERM.SYMBOL (CAR TERMLIST)) GTERM)))
	  ((AND (DB=GTERM.IS.GENERAL (SECOND TERMLIST))
		(NULL (SET-DIFFERENCE VARS RIGHT.VARS))
		(NULL (DA-PREFUN.DEFINITION (DA-GTERM.SYMBOL (SECOND TERMLIST))))
		(DB=SYMBOL.INSERT.DEFINING.SYMBOLS (DA-GTERM.SYMBOL (SECOND TERMLIST)) GTERM))))))


(DEFUN DB=SYMBOL.INSERT.DEFINING.SYMBOLS (SYMBOL GTERM)

  ;;; Input:   a prefun and a gterm
  ;;; Effect:  computes allfunction- and predicate-symbols in \verb$GTERM$ and considers
  ;;;          them as symbols used to define \verb$SYMBOL$.
  ;;; Value:   undefined.

  (LET ((SYMBOLS (DA-GTERM.DEFINING.SYMBOLS GTERM)))
    (COND ((EVERY #'(LAMBDA (PREFUN)
		      (NOT (DA-PREFUN.IS.LESS SYMBOL PREFUN)))
		  SYMBOLS)
	   (SETF (DA-PREFUN.DEFINING.SYMBOLS SYMBOL)
		 (union SYMBOLS (DA-PREFUN.DEFINING.SYMBOLS SYMBOL)))
	   T))))


(DEFUN DB-DEFINITION.INSERT (FORMULA NAME)
  
  ;;; Input:   a list of function- and predicate-definitions 
  ;;;          (e.g. a tupel: tree, if-then-case, symbol and formal parameters)
  ;;; Effect:  inserts all definitions into the database.
  ;;; Value:   List of all gterms, created by these definitions.
  
  (MULTIPLE-VALUE-BIND (DEFINITION SYMBOL FORMAL.PARAMETERS) (VALUES-LIST FORMULA)
    (SETQ DEFINITION (DB=DEFINITION.INSERT DEFINITION SYMBOL FORMAL.PARAMETERS))
    (LET ((COUNTER 0))
      (MAPC #'(LAMBDA (GTERM)
		(SETF (DA-GTERM.PNAME GTERM) (FORMAT NIL "~A.~D" NAME (INCF COUNTER)))
		(DB-GTERM.INSERT GTERM 'AXIOM))
	    DEFINITION))
    DEFINITION))


(DEFUN DB=DEFINITION.INSERT (DEFINITION SYMBOL FORMAL.PARAMETERS)

  ;;; Input:   a definitions, e.g. a tupel: tree, if-then-case, symbol and formal parameters
  ;;; Effect:  inserts the function-definition into the database.
  ;;; Value:   List of all gterms, created by this definition.
  
  (LET (HEADER GTERMS NEW.GTERMS)
    (SETF (DA-PREFUN.FORMAL.PARAMETERS SYMBOL) FORMAL.PARAMETERS)
    (DB=DEFINITION.REC.POSITIONS SYMBOL)
    (SETQ HEADER (COND ((DA-FUNCTION.IS SYMBOL)
			(DA-TERM.CREATE SYMBOL (MAPCAR #'(LAMBDA (X) (DA-TERM.CREATE X)) FORMAL.PARAMETERS) (list :def.header t)))
		       (T (DA-LITERAL.CREATE (DA-SIGN.PLUS) SYMBOL
					     (MAPCAR #'(LAMBDA (X) (DA-TERM.CREATE X)) FORMAL.PARAMETERS)
					     (list :def.header t)))))
    (SETQ DEFINITION (DA-GTERM.DEF.REPLACE.WITH.CONDS
		      (da-gterm.copy DEFINITION)
		      #'(LAMBDA (VALUE CONDITION)
			  (MULTIPLE-VALUE-SETQ (VALUE NEW.GTERMS)
			    (COND ((DA-FUNCTION.IS SYMBOL) 
				   (DB=DEFINITION.FUNCTION.GTERM HEADER VALUE CONDITION))
				  (T (DB=DEFINITION.PREDICATE.GTERM HEADER VALUE CONDITION))))
			  (SETQ GTERMS (NCONC NEW.GTERMS GTERMS))
			  VALUE)))
    (SETF (DA-PREFUN.DEFINITION SYMBOL) DEFINITION)
    (SETF (DA-PREFUN.DEFINING.SYMBOLS SYMBOL) (DA-GTERM.DEFINING.SYMBOLS DEFINITION))
    (cond ((da-function.is symbol) (da=function.is.surjective symbol FORMAL.PARAMETERS)))
    (CONS DEFINITION GTERMS)))


(DEFUN DB=DEFINITION.FUNCTION.GTERM (HEADER VALUE CONDITION)
  
  ;;; Input:   a function-symbol, the formal-parameters, a value of a case, and its condition.
  ;;; Effect:  if condition contains match-literals of variables occuring in \verb$VALUE$ inside a selectorfunction
  ;;;          a simplified version of VALUE is generated.
  
  (LET (LITERALS NEW.HEADER TERM)
    (VALUES (DA-GTERM.DEF.VALUE.CREATE
	     (DA-LITERAL.CREATE (DA-SIGN.PLUS) (DA-PREDICATE.EQUALITY) (LIST (DA-TERM.COPY HEADER) VALUE)
				 (COND ((DA-SYMBOL.OCCURS.IN.GTERM (DA-GTERM.SYMBOL HEADER) VALUE)
					(LIST 'RECURSIVE T)))))
	    (COND ((MULTIPLE-VALUE-SETQ (TERM LITERALS NEW.HEADER) (DB=INSERT.MATCH.IN.VALUE CONDITION HEADER VALUE))
		   (setf (getf (da-gterm.attributes new.header) :def.header) t)
		   (LIST (DA-FORMULA.JUNCTION.CLOSURE
			  'OR
			  (NCONC1 LITERALS
				  (DA-LITERAL.CREATE (DA-SIGN.PLUS) (DA-PREDICATE.EQUALITY)
						     (LIST NEW.HEADER TERM))))))))))


(DEFUN DB=DEFINITION.PREDICATE.GTERM (HEADER VALUE CONDITION)
  
  ;;; Input:   a predicate-symbol, the formal-parameters, a term, and its condition.
  
  (LET (RESULT GTERM LITERALS NEW.HEADER GTERMS OLD.VALUE)
    (COND ((DA-FORMULA.IS.TRUE VALUE)
	   (SETQ RESULT (DA-LITERAL.COPY HEADER)))
	  ((DA-FORMULA.IS.FALSE VALUE)
	   (SETQ RESULT (DA-LITERAL.NEGATE (DA-LITERAL.COPY HEADER))))
	  (T (SETQ OLD.VALUE (DA-GTERM.COPY VALUE))
	     (SETQ RESULT (NORM-NORMALIZATION (DA-FORMULA.CREATE 'EQV (LIST (DA-LITERAL.COPY HEADER) VALUE))))
	     (COND ((DA-SYMBOL.OCCURS.IN.GTERM (DA-GTERM.SYMBOL HEADER) VALUE)
		    (SETF (GETF (DA-GTERM.ATTRIBUTES RESULT) 'RECURSIVE)  T)))
	     (COND ((MULTIPLE-VALUE-SETQ (GTERM LITERALS NEW.HEADER)
		      (DB=INSERT.MATCH.IN.VALUE CONDITION (DA-LITERAL.COPY HEADER) OLD.VALUE))
		    (setf (getf (da-gterm.attributes new.header) :def.header) t)
		    (PUSH (DA-FORMULA.JUNCTION.CLOSURE
			   'OR (NCONC LITERALS (LIST (NORM-NORMALIZATION
						      (DA-FORMULA.CREATE 'EQV (LIST NEW.HEADER GTERM))))))
			  GTERMS)))))
    (VALUES (DA-GTERM.DEF.VALUE.CREATE RESULT) GTERMS)))


(DEFUN DB=DEFINITION.REC.POSITIONS (SYMBOL)
  (SETF (DA-PREFUN.REC.POSITIONS SYMBOL)
        (REMOVE-DUPLICATES (MAPCAN #'(LAMBDA (WFO.SUG)
					     (COPY-LIST (DA-WFOSUG.POSITIONS WFO.SUG)))
                                   (DA-PREFUN.WFO.SUGGESTED SYMBOL)))))


(DEFUN DB=INSERT.MATCH.IN.VALUE (CONDITION HEADER VALUE)

  ;;; Input:  a list of literals, a head-term of a function definition and the value of an case
  ;;; Effect: removes the selector-terms in VALUE by the help of the match-literals in \verb$CONDITION$.
  ;;;         e.g. if $x = s(p(x))$ is member of \verb$CONDITION$, $x$ is replaced by a term $s(u)$ and $p(s(x))$ is
  ;;;         replaced by $u$.
  ;;; Value:  the changed \verb$CONDITION$, \verb$HEADER$ and \verb$VALUE$.
  
  (LET (SEL.TERM SUBST)
       (SETQ CONDITION
	     (REMOVE-IF #'(LAMBDA (LITERAL)
				  (COND ((AND (DA-LITERAL.IS LITERAL)
					      (DA-LITERAL.IS.MATCH LITERAL)
					      (DA-SORT.IS.FREE.STRUCTURE  (DA-TERM.SORT (CAR (DA-LITERAL.TERMLIST LITERAL)))))
					 (SETQ SEL.TERM (CAR (DA-LITERAL.TERMLIST LITERAL)))
					 (COND ((OR (NULL (DA-TERM.TERMLIST (SECOND (DA-LITERAL.TERMLIST LITERAL))))
						    (LET ((TAFS (DA-GTERM.OCCURS.IN.GTERM SEL.TERM VALUE)) symbol)
						      (OR (NULL TAFS)
							  (SOME #'(LAMBDA (TAF)
								    (cond (taf (setq symbol (DA-GTERM.SYMBOL (DA-ACCESS (CDR TAF) VALUE)))
									       (AND (da-function.is symbol)
										    (DA-FUNCTION.IS.SELECTOR symbol)))))
								(DA-GTERM.OCCURS.IN.GTERM SEL.TERM VALUE)))))
						(SETQ SUBST (DB=INSERT.MATCH.COMPUTE.SUBST SUBST LITERAL)))))))
			CONDITION))
       (COND (SUBST
	      (VALUES (DB=GTERM.REDUCE (UNI-SUBST.APPLY SUBST VALUE T))
		      (MAPCAR #'(LAMBDA (LIT) (DB=GTERM.REDUCE (UNI-SUBST.APPLY SUBST LIT T))) CONDITION)
		      (UNI-SUBST.APPLY SUBST HEADER T))))))


(DEFUN DB=INSERT.MATCH.COMPUTE.SUBST (SUBST LITERAL)

  ;;; Input:  a substitution and a match-literal
  ;;; Effect: updates substitution by the replacement of the selectorterms defined by \verb$LITERAL$.
  ;;; Value:  the adapted substitution.
  
  (LET ((SEL.TERM (CAR (DA-LITERAL.TERMLIST LITERAL)))
	(TERM (DA-FUNCTION.CREATE.TERM (DA-TERM.SYMBOL (SECOND (DA-LITERAL.TERMLIST LITERAL))))))
       (COND ((NOT (DA-VARIABLE.IS (DA-TERM.SYMBOL SEL.TERM)))
	      (SETQ SEL.TERM (DB=GTERM.REDUCE (UNI-SUBST.APPLY SUBST SEL.TERM T)))))
       (CAR (UNI-SUBST.MERGE (CAR (UNI-TERM.MATCH SEL.TERM TERM T)) SUBST))))


(DEFUN DB=GTERM.REDUCE (GTERM)

  ;;; Input:   a term
  ;;; Effect:  reduces term by structural equations like $p(s(x)) = x$.
  ;;; Value:   the reduced term
  
  (SETF (DA-GTERM.TERMLIST GTERM)
        (MAPCAR #'(LAMBDA (SUBTERM) (DB=GTERM.REDUCE SUBTERM)) (DA-GTERM.TERMLIST GTERM)))
  (COND ((AND (DA-FUNCTION.IS (DA-GTERM.SYMBOL GTERM))
              (DA-FUNCTION.IS.SELECTOR (DA-GTERM.SYMBOL GTERM))
              (EQ (DA-SORT.CONSTRUCTOR.OF.SELECTOR (DA-GTERM.SYMBOL GTERM))
                  (DA-GTERM.SYMBOL (CAR (DA-GTERM.TERMLIST GTERM))))
              (da-sort.is.free.structure (car (da-function.domain.sorts (DA-GTERM.SYMBOL GTERM)))))
         (NTH (POSITION (DA-GTERM.SYMBOL GTERM)
			(DA-SORT.SELECTORS.OF.CONSTRUCTOR (DA-GTERM.SYMBOL (CAR (DA-GTERM.TERMLIST GTERM)))))
              (DA-GTERM.TERMLIST (CAR (DA-GTERM.TERMLIST GTERM)))))
        (T GTERM)))


(DEFUN DB-THEOREMS () DB*THEOREMS)


(DEFMACRO DB-WITH.GTERMS.INSERTED (GTERMS TYPE PROP &REST BODY)

  ;;; Input:   a list of gterms, an atom and a flag
  ;;; Effect:  inserts gterms into the database, evaluates body and then, deletes gterms again
  ;;;          from the database.
  ;;; Value:   the result of the evaluation of body.

  `(LET ((ALL.GTERMS ,GTERMS))
     (UNWIND-PROTECT (PROGN (MAPC #'(LAMBDA (GTERM)
				      (SETF (DA-GTERM.PNAME GTERM) "Theorem")
				      (DB-GTERM.INSERT GTERM ,TYPE ,PROP))
				  ALL.GTERMS)
			    (PROGN . ,BODY))
       (MAPC #'(LAMBDA (GTERM) (DB-GTERM.DELETE GTERM)) (REVERSE ALL.GTERMS)))))



(DEFUN DB-GTERM.INSERT (GTERM &OPTIONAL TYPE PROP)
  
  ;;; Input:   a gterm, an atom and a flag
  ;;; Effect:  inserts \verb$GTERM$ into the database.
  ;;; Value:   undefined.
  
  (COND ((NOT (GETF (DA-GTERM.ATTRIBUTES GTERM) 'ACTIVE))
	 (SETF (GETF (DA-GTERM.ATTRIBUTES GTERM) 'ACTIVE) T)
	 (cond ((eq type 'theorem) (push gterm db*theorems)))
	 (DED-INPUT.HISTORY.INSERT `(DB-GTERM.DELETE (QUOTE ,GTERM)))
	 (setf (getf (da-gterm.attributes gterm) 'defining.input) (DED-INPUT.ACTUAL.INPUT))
	 (DB=GTERM.INSERT.CROSS.REFERENCES GTERM TYPE PROP)
	 (COND ((AND (NOT PROP) (MEMBER TYPE '(AXIOM LEMMA)))
		(DB=GTERM.INSERT.ATTRIBUTES GTERM))))))


(DEFUN DB-GTERM.DELETE (GTERM &OPTIONAL REMOVE.FROM.HISTORY)
  
  ;;; Input:   a gterm
  ;;; Effect:  deletes \verb$GTERM$ out of the database.
  ;;; Value:   undefined.

  (COND ((GETF (DA-GTERM.ATTRIBUTES GTERM) 'ACTIVE)
	 (SETF (GETF (DA-GTERM.ATTRIBUTES GTERM) 'ACTIVE) NIL)
	 (setq db*theorems (delete GTERM db*theorems))
	 (MAPC #'(LAMBDA (HISTORY) (FUNCALL HISTORY)) (GETF (DA-GTERM.ATTRIBUTES GTERM) 'HISTORY))
	 (DB=MODIFIER.REMOVE.ALL GTERM)
	 (COND (REMOVE.FROM.HISTORY (DED-INPUT.HISTORY.DELETE `(DB-GTERM.DELETE (QUOTE ,GTERM))))))))


(DEFMACRO DB-WITH.ACTIVE.PROP.GTERMS (GTERMS TYPE ORIGIN &REST BODY)

  ;;; Input:  a list of gterms,  an symbol and a lists of sexpressions
  ;;; Effect: executes \verb$BODY$ within the activated \verb$GTERMS$. After this execution
  ;;;         the activated \verb$GTERMS$ will be deactivated.
  ;;; Value:  the value of the execution of \verb$BODY$.
  
  `(LET ((ALL.GTERMS ,GTERMS))
     (UNWIND-PROTECT (PROGN (MAPC #'(LAMBDA (GTERM) (DB-GTERM.INSERT GTERM ,TYPE ,ORIGIN)) ALL.GTERMS)
			    (PROGN . ,BODY))
       (MAPC #'(LAMBDA (GTERM) (DB-GTERM.DELETE GTERM t)) (REVERSE ALL.GTERMS)))))


(DEFUN DB=GTERM.INSERT.CROSS.REFERENCES (GTERM TYPE PROP)

  ;;; Input:   a gterm
  ;;; Effect:  inserts \verb$GTERM$ in global lists of literals or gterms with special attributes
  ;;;          e.g. colour-informations are computed and added to the database.
  ;;; Value:   undefined

  (LET ((VARIABLES (DA-GTERM.VARIABLES GTERM)))
    (MULTIPLE-VALUE-BIND (EQUATIONS IMPLICATIONS PUMPING.EQUATIONS)
      (DB=GTERM.FIND.IMPLICATIONS.AND.EQUATIONS GTERM (DB=GTERM.SAMPLE.LITS GTERM NIL NIL GTERM))
      (COND ((NOT PROP)
	     (MAPC #'(LAMBDA (SYMBOL.TAF.TAFLIST)
		       (MAPC #'(LAMBDA (TAF.TAFLIST)
				 (DB=GTERM.INSERT.IMPLICATION
				  GTERM (CAR TAF.TAFLIST) (CDR TAF.TAFLIST) TYPE))
			     (CDR SYMBOL.TAF.TAFLIST)))
		   IMPLICATIONS)
	     (MAPC #'(LAMBDA (LITERAL.TAF)
		       (COND ((NULL (SET-DIFFERENCE VARIABLES (DA-GTERM.VARIABLES (CAR LITERAL.TAF))))
			      (DB=GTERM.INSERT.EQUATION GTERM (CDR LITERAL.TAF) TYPE))))
		   EQUATIONS)
	     (MAPC #'(LAMBDA (LITERAL.TAF)
		       (DB=GTERM.INSERT.PUMPING.EQUATION GTERM (CDR LITERAL.TAF)))
		   PUMPING.EQUATIONS)))      
      (DB=GTERM.INSERT.LITS GTERM NIL 0 GTERM TYPE PROP))))


;;;;; computing all interesting equations and implications P(...) -> P(...) :


(DEFUN DB=GTERM.INSERT.LITS (GTERM &OPTIONAL TAF LENGTH GLOBAL.GTERM TYPE PROP)

  ;;; Input:  a gterm, a gterm-access-function, a number, and another gterm

  (COND ((NOT (DB=GTERM.ACTUAL.GTERM.IS.PART.OF.IMPL.OR.EQ GTERM))
	 (COND ((DA-LITERAL.IS GTERM)
		(cond ((not prop)
		       (DB=LITERAL.INT.INEQUALITY GTERM TAF GLOBAL.GTERM)
		       (COND ((AND TAF (GETF (DA-GTERM.ATTRIBUTES GTERM) 'EQV))
			      (DB=GTERM.CHECK.FOR.SIMPL.RULE GTERM TAF GLOBAL.GTERM TYPE)))))
		(DB=PREFUN.DATABASE.ADD
		 (DA-LITERAL.SYMBOL GTERM) (DA-LITERAL.SIGN GTERM) (LIST GTERM LENGTH (COND (PROP) (T GLOBAL.GTERM)) taf TYPE)
		 #'(LAMBDA (X Y) (OR (AND (EQ (FIFTH (CDR X)) 'THEOREM) (NEQ (FIFTH (CDR Y)) 'THEOREM))
				     (< (SECOND (CDR X)) (SECOND (CDR Y)))))
		 GLOBAL.GTERM))
	       (T (LET ((TAF (DA-TAF.CREATE.ZERO TAF)))
		    (COND ((EQ 'OR (DA-GTERM.SYMBOL GTERM))
			   (INCF LENGTH (LENGTH (DA-GTERM.TERMLIST GTERM)))))
		    (MAPC #'(LAMBDA (SUB.TERM)
			      (SETQ TAF (DA-TAF.CREATE.NEXT TAF))
			      (DB=GTERM.INSERT.LITS SUB.TERM TAF LENGTH GLOBAL.GTERM TYPE prop))
			  (DA-GTERM.TERMLIST GTERM))))))
	 (T (LET (LITERAL)
	      (MAPC #'(LAMBDA (SUB.TAF)
			(SETQ LITERAL (DA-ACCESS SUB.TAF GTERM))
			(SETQ SUB.TAF (NCONC SUB.TAF TAF))
			(cond ((not prop) 
			       (DB=LITERAL.INT.INEQUALITY LITERAL SUB.TAF GLOBAL.GTERM)
			       (COND ((AND SUB.TAF (GETF (DA-GTERM.ATTRIBUTES LITERAL) 'EQV))
				      (DB=GTERM.CHECK.FOR.SIMPL.RULE LITERAL SUB.TAF GLOBAL.GTERM TYPE)))))
			(DB=PREFUN.DATABASE.ADD (DA-LITERAL.SYMBOL LITERAL)
						(cond ((da-sign.is.positive (DA-LITERAL.SIGN LITERAL)) '++)
						      (t '--))
						(LIST LITERAL 0 (COND (PROP) (T GLOBAL.GTERM)) SUB.TAF)
						NIL GLOBAL.GTERM))
		  (DA-GTERM.TAFS GTERM #'(LAMBDA (GTERM) (DA-LITERAL.IS GTERM))))))))


(DEFUN DB=GTERM.CHECK.FOR.SIMPL.RULE (GTERM TAF GLOBAL.GTERM TYPE)

  (LET (VALUE INPUT.SYMBOLS VALUE.SYMBOLS)
    (COND ((DA-FORMULA.IS.FALSE (DA-GTERM.WITHOUT.TAFS GLOBAL.GTERM (CDR TAF)))
	   (SETQ VALUE (DA-GTERM.WITHOUT.TAFS (DA-ACCESS (CDR TAF) GLOBAL.GTERM) (LIST (CAR TAF))))
	   (SETQ INPUT.SYMBOLS (DA-PREFUN.INDEPENDENT.SYMBOLS (DA-GTERM.PREFUNS GTERM)))
	   (SETQ VALUE.SYMBOLS (DA-PREFUN.INDEPENDENT.SYMBOLS (DA-GTERM.PREFUNS VALUE)))
	   (COND ((AND (SET-DIFFERENCE INPUT.SYMBOLS VALUE.SYMBOLS)
		       (EVERY #'(LAMBDA (SYMBOL)
				  (NOT (DA-PREFUN.IS.INDEPENDENT SYMBOL INPUT.SYMBOLS)))
			      VALUE.SYMBOLS))
		  (DB=MODIFIER.INSERT GTERM 'SIMPLIFICATIONS GTERM VALUE NIL NIL GLOBAL.GTERM
				      taf (LIST 'TYPE TYPE))))))))
			     


(DEFUN DB=GTERM.ACTUAL.GTERM.IS.PART.OF.IMPL.OR.EQ (GTERM)

  ;;; Input:   a gterm
  ;;; Effect:  tests whether each path through \verb$GTERM$ contains either an equality or
  ;;;          a part of an implication.
  ;;; Value:   T, if it is the case, NIL else.

  (COND ((DA-LITERAL.IS GTERM)
	 (GETF (DA-LITERAL.ATTRIBUTES GTERM) 'IMPLICATION))
	((EQ 'OR (DA-GTERM.SYMBOL GTERM))
	 (SOME #'(LAMBDA (SUB.TERM)
		   (DB=GTERM.ACTUAL.GTERM.IS.PART.OF.IMPL.OR.EQ SUB.TERM))
	       (DA-GTERM.TERMLIST GTERM)))
	((EQ 'AND (DA-GTERM.SYMBOL GTERM))
	 (EVERY #'(LAMBDA (SUB.TERM)
		    (DB=GTERM.ACTUAL.GTERM.IS.PART.OF.IMPL.OR.EQ SUB.TERM))
	       (DA-GTERM.TERMLIST GTERM)))))


(DEFUN DB=GTERM.SAMPLE.LITS (GTERM &OPTIONAL TAF OCC.LIST TOP.GTERM)

  ;;; Input:  a gterm, a gterm-access-function, a list of (predicate taf.list1 taf.list2) and a gterm
  ;;; Effect: samples all occurrences of predicate symbols in GTERM
  ;;; Value:  a list of (predicate taf.list1 taf.list2), where taf.list1 denotes the positive occurrences
  ;;;         of predicate in TOP.GTERM and taf.list2 the negative ones.
  
  (COND ((DA-LITERAL.IS GTERM)
	 (SETF (GETF (DA-LITERAL.ATTRIBUTES GTERM) 'TOP.LEVEL.GTERM) TOP.GTERM)
	 (SETF (GETF (DA-LITERAL.ATTRIBUTES GTERM) 'TAF) TAF)
	 (SETF (GETF (DA-GTERM.ATTRIBUTES GTERM) 'IMPLICATION) NIL)
	 (PUSH TAF (GETF (GETF OCC.LIST (DA-LITERAL.SYMBOL GTERM)) (DA-LITERAL.SIGN GTERM))))
	(T (LET ((TAF (DA-TAF.CREATE.ZERO TAF)))
	     (MAPC #'(LAMBDA (SUB.TERM)
		       (SETQ TAF (DA-TAF.CREATE.NEXT TAF))
		       (SETQ OCC.LIST (DB=GTERM.SAMPLE.LITS SUB.TERM TAF OCC.LIST TOP.GTERM)))
		   (DA-GTERM.TERMLIST GTERM)))))
  OCC.LIST)


(DEFUN DB=GTERM.FIND.IMPLICATIONS.AND.EQUATIONS (GTERM OCC.LIST)

  ;;; Input:  a gterm and a list of (predicate taf.list1 taf.list2) as described above
  ;;; Effect: collects all equations (occurring all variables of \verb$GTERM$ in it) and all possible implications
  ;;; Value : a multiple value consisting of equations and implications.
  
  (LET ((VARS (DA-GTERM.VARIABLES GTERM)) EQUATIONS IMPLICATIONS PUMPING.EQUATIONS ALL.IMPLICATIONS LIT)
    (MAPCF #'(LAMBDA (SYMBOL TAF.LIST)
	       (COND ((DA-PREDICATE.IS.EQUALITY SYMBOL)
		      (MAPC #'(LAMBDA (POS.TAF)
				(SETQ LIT (DA-ACCESS POS.TAF GTERM))
				(COND ((AND (SUBSETP VARS (DA-GTERM.VARIABLES LIT))
					    (NOT (DB=equation.is.pumping lit)))
				       (SETF (GETF (DA-GTERM.ATTRIBUTES LIT) 'IMPLICATION) T)
				       (PUSH (CONS LIT POS.TAF) EQUATIONS))
				      (T (PUSH (CONS LIT POS.TAF) PUMPING.EQUATIONS))))
			    (GETF TAF.LIST (DA-SIGN.PLUS)))))
	       (MAPC #'(LAMBDA (POS.TAF)
			 (MAPC #'(LAMBDA (NEG.TAF)
				   (COND ((DB=GTERM.TAF.ARE.COMPATIBLE GTERM SYMBOL POS.TAF NEG.TAF)
					  ;(cond ((not (DA-PREDICATE.IS.EQUALITY SYMBOL))))
					  (SETQ IMPLICATIONS (DB=GTERM.INSERT.TAF.RELATION
								     IMPLICATIONS NEG.TAF POS.TAF))
					  (SETQ IMPLICATIONS (DB=GTERM.INSERT.TAF.RELATION
							      IMPLICATIONS POS.TAF NEG.TAF)))))
			       (GETF TAF.LIST (DA-SIGN.MINUS))))
		     (GETF TAF.LIST (DA-SIGN.PLUS)))
	       (COND (IMPLICATIONS (PUSH (CONS SYMBOL IMPLICATIONS) ALL.IMPLICATIONS))))
	   OCC.LIST)
    (VALUES EQUATIONS ALL.IMPLICATIONS PUMPING.EQUATIONS)))


(defun DB=equation.is.pumping (lit)

  (let ((t1 (car (da-literal.termlist lit))) (t2 (second (da-literal.termlist lit))))
    (or (and (da-variable.is (da-term.symbol t1))
	     (not (member (da-term.symbol t1) (da-gterm.variables t2))))
	(and (da-variable.is (da-term.symbol t2))
	     (not (member (da-term.symbol t2) (da-gterm.variables t1)))))))


(DEFUN DB=GTERM.INSERT.TAF.RELATION (IMPLICATIONS TAF1 TAF2)

  (LET (ENTRY)
       (COND ((SETQ ENTRY (ASSOC TAF1 IMPLICATIONS))
	      (PUSH TAF2 (CDR ENTRY))
	      IMPLICATIONS)
	     (T (ACONS TAF1 (LIST TAF2) IMPLICATIONS)))))


(DEFUN DB=GTERM.TAF.ARE.COMPATIBLE (GTERM SYMBOL POS.TAF NEG.TAF)

  ;;; TO BE REMOVED FROM THIS MODULE !

  (LET* ((POS.LENGTH (LENGTH POS.TAF))
	 (NEG.LENGTH (LENGTH NEG.TAF))
	 (MIN.LENGTH (MIN NEG.LENGTH POS.LENGTH))
	 SUB.TERM POS.SUB.TAF NEG.SUB.TAF)
    (SETQ POS.SUB.TAF (NTHCDR (1+ (- POS.LENGTH MIN.LENGTH)) POS.TAF))
    (SETQ NEG.SUB.TAF (NTHCDR (1+ (- NEG.LENGTH MIN.LENGTH)) NEG.TAF))
    (COND ((EQUAL POS.SUB.TAF NEG.SUB.TAF)
	   (SETQ SUB.TERM  (DA-ACCESS POS.SUB.TAF GTERM))
	   (COND ((EQ 'OR (DA-GTERM.SYMBOL SUB.TERM))
		  (COND ((EQ (MAX NEG.LENGTH POS.LENGTH) NEG.LENGTH)
			 (SETF (GETF (DA-GTERM.ATTRIBUTES (DA-ACCESS NEG.TAF GTERM)) 'IMPLICATION) T)))
		  (COND ((EQ (MAX NEG.LENGTH POS.LENGTH) POS.LENGTH)
			 (SETF (GETF (DA-GTERM.ATTRIBUTES (DA-ACCESS POS.TAF GTERM)) 'IMPLICATION) T)))
		  (LIST SYMBOL POS.TAF NEG.TAF)))))))


(DEFUN DB=GTERM.TOP.OF.DIFF (GTERM1 GTERM2)

  ;;; Input:   two gterms
  ;;; Effect:  compares both gterms and determines a minimal subterm of both gterms such
  ;;;          that \verb$GTERM1$ and \verb$GTERM2$ differ only in this subterm
  ;;; Value:   the access taf to this subterm, else NIL

  (LET (CHANGED.POS TAF (POS 0))
    (COND ((EVERY #'(LAMBDA (SUBTERM1 SUBTERM2)
		      (INCF POS)
		      (COND (CHANGED.POS (UNI-GTERM.ARE.EQUAL SUBTERM1 SUBTERM2))
			    ((SETQ TAF (DB=GTERM.TOP.OF.DIFF SUBTERM1 SUBTERM2))
			     (SETQ TAF (NCONC TAF (LIST POS))))))
		  (DA-GTERM.TERMLIST GTERM1)
		  (DA-GTERM.TERMLIST GTERM2))
	   TAF))))


;;;;; sorting equations and implications due to their properties:


(DEFUN DB=GTERM.INSERT.IMPLICATION (GTERM TAF CORRESPONDING.TAFS TYPE)

  ;;; Input:   a gterm, a taf (denoting the input of a modifier), a list of tafs (denoting those
  ;;;          literals which have to belong to the value of the modifier), and an atom (denoting
  ;;;          the type of gterm.)
  ;;; Effect:  inserts all possible modifier into the database.
  ;;; Value:   undefined

  (LET ((COMMON.TAF (DA-TAF.COMMON.TAF CORRESPONDING.TAFS)) INPUT VALUE CONDITION C.T)
    (SETQ INPUT (DA-ACCESS TAF GTERM))
    (COND ((NOT (DA-TAF.IS.SUBTAF COMMON.TAF TAF))
	   (COND ((NOT (GETF (DA-GTERM.ATTRIBUTES INPUT) 'EQV))
		  (SETQ C.T (DA-TAF.COMMON.TAF (LIST TAF COMMON.TAF)))
		  (SETQ COMMON.TAF (LASTN COMMON.TAF (1+ (LENGTH C.T))))
		  (SETQ VALUE (DA-ACCESS COMMON.TAF GTERM))
		  (SETQ CONDITION (DA-GTERM.WITHOUT.TAFS GTERM TAF COMMON.TAF)))
		 (T (SETQ C.T (DA-TAF.COMMON.TAF (LIST TAF COMMON.TAF)))
		    (SETQ VALUE (DA-GTERM.WITHOUT.TAFS (DA-ACCESS C.T GTERM)
						       (DA-TAF.DIFFERENCE.OF.TWO.TAFS TAF C.T)))
		    (SETQ CONDITION (DA-GTERM.WITHOUT.TAFS GTERM C.T)))))
	  (T (SETQ VALUE (DA-GTERM.WITHOUT.TAFS (DA-ACCESS COMMON.TAF GTERM)
						(DA-TAF.DIFFERENCE.OF.TWO.TAFS TAF COMMON.TAF)))
	     (SETQ CONDITION (DA-GTERM.WITHOUT.TAFS GTERM COMMON.TAF))))
    (DB=GTERM.INSERT.MODIFIERS INPUT VALUE (DA-FORMULA.JUNCTION.OPEN 'OR CONDITION) GTERM TAF TYPE)))


(DEFUN DB=GTERM.INSERT.EQUATION (GTERM TAF TYPE)

  ;;; Input:   a gterm, a term-access-function denoting an equation, and the type of gterm
  ;;; Effect:  inserts all possible modifiers derivated from the equation in \verb$GTERM$ into the database.
  ;;; Value:   undefined.

  (LET ((LITERAL (DA-ACCESS TAF GTERM))
	(CONDITION (DA-FORMULA.JUNCTION.OPEN 'OR (DA-GTERM.WITHOUT.TAFS GTERM TAF))))
    (DB=GTERM.INSERT.MODIFIERS (CAR (DA-LITERAL.TERMLIST LITERAL))
			       (SECOND (DA-LITERAL.TERMLIST LITERAL))
			       CONDITION GTERM (da-taf.create.left taf) TYPE 
			       (da-taf.create.right taf))))


(DEFUN DB=GTERM.INSERT.PUMPING.EQUATION (GTERM TAF)

  (LET ((LITERAL (DA-ACCESS TAF GTERM))
	(CONDITION (DA-FORMULA.JUNCTION.OPEN 'OR (DA-GTERM.WITHOUT.TAFS GTERM TAF))))
    (DB=GTERM.INSERT.PUMPING.MODIFIERS (CAR (DA-LITERAL.TERMLIST LITERAL))
				       (SECOND (DA-LITERAL.TERMLIST LITERAL))
				       CONDITION GTERM (da-taf.create.left taf))
    (DB=GTERM.INSERT.PUMPING.MODIFIERS (SECOND (DA-LITERAL.TERMLIST LITERAL))
				       (CAR (DA-LITERAL.TERMLIST LITERAL))
				       CONDITION GTERM (da-taf.create.right taf))))


(DEFUN DB=GTERM.INSERT.PUMPING.MODIFIERS (INPUT VALUE CONDITION ORG.GTERM org.taf)

  ;;; Function  : db=gterm.insert.top.level.modifiers
  ;;; Author    : SA
  ;;; Edited    : 17.12.1993
  ;;; Arguments : two gterms (of an equation or an implication), the condition and the top level gterm
  ;;; Effect    : inserts modifiers of type f(...) -> g(...)
  ;;; Value     : ?

  (LET ((SYMBOL1 (DA-GTERM.SYMBOL INPUT)))
    (COND ((DA-prefun.is symbol1)
	   (DB=MODIFIER.INSERT INPUT 'PUMPING INPUT VALUE NIL
			       CONDITION ORG.GTERM org.taf ))
	  ((DA-VARIABLE.IS SYMBOL1)
	   (DB=MODIFIER.INSERT (DA-VARIABLE.SORT SYMBOL1) 'PUMPING INPUT VALUE NIL CONDITION
			       ORG.GTERM org.taf NIL)))))


(DEFUN DB=GTERM.IS.GENERAL (GTERM)

  ;;; Input:   a gterm
  ;;; Effect:  tests whether \verb$GTERM$ is either a literal or a term, such that its termlist contains
  ;;;          only variables and selector/constructor-functions and no variable occur in different
  ;;;          arguments
  ;;; Value:   T, if the condition above is true.

  (LET ((SYMBOL (DA-GTERM.SYMBOL GTERM)) ALL.VARS VARS)
    (AND (DA-GTERM.TERMLIST GTERM)
	 (COND ((DA-PREDICATE.IS SYMBOL)
		(NOT (DA-PREDICATE.IS.EQUALITY SYMBOL)))
	       ((DA-FUNCTION.IS SYMBOL)
		(AND (NOT (DA-FUNCTION.IS.SELECTOR SYMBOL))
		     (NOT (DA-FUNCTION.IS.CONSTRUCTOR SYMBOL)))))
	 (EVERY #'(LAMBDA (TERM)
		    (AND (EVERY #'(LAMBDA (SYMBOL1)
				    (OR (DA-FUNCTION.IS.SELECTOR SYMBOL1)
					(DA-FUNCTION.IS.CONSTRUCTOR SYMBOL1)))
				(DA-GTERM.FUNCTIONS TERM))
			 (PROG1 (NULL (INTERSECTION ALL.VARS (SETQ VARS (DA-GTERM.VARIABLES TERM))))
			   (SETQ ALL.VARS (NCONC VARS ALL.VARS)))))				
		(DA-GTERM.TERMLIST GTERM)))))   


(DEFUN DB=GTERM.INSERT.MODIFIERS (INPUT VALUE CONDITION ORG.GTERM ORG.TAF TYPE &optional both.directions)

  ;;; Input:  two gterms a list of gterms the original gterm and an sexpression
  ;;; Effect: inserts all modifiers generated by the rule input -> value.
  ;;; Value:  undefined

  (DB=GTERM.INSERT.COLOUR.MODIFIERS INPUT VALUE CONDITION ORG.GTERM ORG.TAF TYPE both.directions)
  (DB=GTERM.INSERT.SIMPL.MODIFIER INPUT VALUE NIL CONDITION ORG.GTERM ORG.TAF TYPE)
  (DB=GTERM.INSERT.RECURSIVE.MODIFIERS INPUT VALUE CONDITION ORG.GTERM ORG.TAF TYPE)
  (DB=GTERM.INSERT.CHANGING.MODIFIERS INPUT VALUE CONDITION ORG.GTERM ORG.TAF)
  (DB=GTERM.INSERT.TOP.LEVEL.MODIFIERS INPUT VALUE CONDITION ORG.GTERM ORG.TAF)
  (DB=GTERM.INSERT.DISMSET.MODIFIERS INPUT VALUE CONDITION ORG.GTERM ORG.TAF)
  (DB=GTERM.INSERT.VARIABLE.MODIFIERS INPUT VALUE CONDITION ORG.GTERM ORG.TAF)
  (cond (both.directions
	 (setq org.taf both.directions)
	 (DB=GTERM.INSERT.SIMPL.MODIFIER VALUE INPUT NIL CONDITION ORG.GTERM ORG.TAF TYPE)
	 (DB=GTERM.INSERT.RECURSIVE.MODIFIERS VALUE INPUT CONDITION ORG.GTERM ORG.TAF TYPE)
	 (DB=GTERM.INSERT.CHANGING.MODIFIERS VALUE INPUT CONDITION ORG.GTERM ORG.TAF)
	 (DB=GTERM.INSERT.TOP.LEVEL.MODIFIERS VALUE INPUT CONDITION ORG.GTERM ORG.TAF)
	 (DB=GTERM.INSERT.DISMSET.MODIFIERS VALUE INPUT CONDITION ORG.GTERM ORG.TAF)
	 (DB=GTERM.INSERT.VARIABLE.MODIFIERS VALUE INPUT CONDITION ORG.GTERM ORG.TAF))))


(DEFUN DB=LITERAL.INT.INEQUALITY (LITERAL TAF GLOBAL.GTERM)

  ;;; Input:   a literal its taf inside the given top-level gterm
  ;;; Effect:  if literal denotes a top-level inequality this inequality
  ;;;          is stored into the database.
  ;;; Value:   undefined

  (LET ((SYMBOL (DA-LITERAL.SYMBOL LITERAL))
	(TERMLIST (DA-LITERAL.TERMLIST LITERAL)))
   (COND ((OR (EQ SYMBOL (DP-PREDICATE.INT.LE))
	      (EQ SYMBOL (DP-PREDICATE.INT.LEQ))
	      (EQ SYMBOL (DP-PREDICATE.INT.GE))
	      (EQ SYMBOL (DP-PREDICATE.INT.GEQ)))
	  (DB=LITERAL.INSERT.LE (EG-EVAL LITERAL)
				(DA-FORMULA.JUNCTION.OPEN 'AND (DA-GTERM.WITHOUT.TAFS GLOBAL.GTERM TAF))
				TAF GLOBAL.GTERM))
	 ((DA-PREDICATE.IS.EQUALITY SYMBOL)
	   (COND ((EQ (DA-TERM.SYMBOL (CAR TERMLIST)) (DP-FUNCTION.INT.SIGN))
		  (DB=LITERAL.INSERT.LE LITERAL
					(DA-FORMULA.JUNCTION.OPEN 'AND (DA-GTERM.WITHOUT.TAFS GLOBAL.GTERM TAF))
					TAF GLOBAL.GTERM))
		 ((AND (EQ (DP-SORT.INT) (DA-TERM.SORT (CAR TERMLIST)))
		       (EQ (DP-SORT.INT) (DA-TERM.SORT (SECOND TERMLIST))))
		  (DB=LITERAL.INSERT.EQ LITERAL
					(DA-FORMULA.JUNCTION.OPEN 'AND (DA-GTERM.WITHOUT.TAFS GLOBAL.GTERM TAF))
					TAF GLOBAL.GTERM)))))))


(DEFUN DB=LITERAL.INSERT.LE (LITERAL CONDITION TAF GLOBAL.GTERM)

  ;;; Input:   a literal denoting an inequality
  ;;; Effect:  inserts this inequality into the database.
  ;;; Value:   undefined

  (LET ((VALUE (DA-TERM.SYMBOL (SECOND (DA-LITERAL.TERMLIST LITERAL))))
	(SIGN (DA-LITERAL.SIGN LITERAL)) SUM KIND)
    (COND ((SETQ KIND (COND ((AND (DA-SIGN.IS.NEGATIVE SIGN)
				  (EQ (DP-FUNCTION.SIGN.+) VALUE))
			     'NEGATED)
			    ((AND (DA-SIGN.IS.POSITIVE SIGN)
			   (EQ (DP-FUNCTION.SIGN.-) VALUE))
			     'NEGATED)
			    ((EQ (DP-FUNCTION.SIGN.+) VALUE)
			     'POSITIVE)))
	   (SETQ SUM (DP=INT.TERM.SUM.CREATE
		      (DP-INT.TERM.NORMALIZE
		       (CAR (DA-TERM.TERMLIST (CAR (DA-LITERAL.TERMLIST LITERAL)))))))
	   (COND ((EQ KIND 'NEGATED)
		  (SETQ SUM (DP=INT.SUM.ADD.SUM SUM -1 (list (cons nil -1)) 1))))
	   (DB=INT.SUM.INSERT SUM CONDITION TAF GLOBAL.GTERM)))))


(DEFUN DB=LITERAL.INSERT.EQ (LITERAL CONDITION TAF GLOBAL.GTERM)

  ;;; Input:   a literal denoting an equality on integers
  ;;; Effect:  inserts this equality as to inequalities into the database.
  ;;; Value:   undefined

  (COND ((DA-SIGN.IS.POSITIVE LITERAL)
	 (LET* ((TERMLIST (DA-LITERAL.TERMLIST LITERAL)))
	   (DB=INT.SUM.INSERT (DP=INT.SUM.ADD.SUM (DP=INT.TERM.SUM.CREATE (DP-INT.TERM.NORMALIZE (CAR TERMLIST))) 1
						  (DP=INT.TERM.SUM.CREATE (DP-INT.TERM.NORMALIZE (SECOND TERMLIST))) -1)
			      CONDITION TAF GLOBAL.GTERM 'EQUALITY)))
	(T (LET ((SUM1 (DP=INT.TERM.SUM.CREATE (DP-INT.TERM.NORMALIZE (CAR (DA-LITERAL.TERMLIST LITERAL)))))
		 (SUM2 (DP=INT.TERM.SUM.CREATE (DP-INT.TERM.NORMALIZE (SECOND (DA-LITERAL.TERMLIST LITERAL))))))
	     (DB=INT.SUMS.INSERT (DP=INT.SUM.ADD.SUM (DP=INT.SUM.ADD.SUM (LIST (CONS NIL -1)) 1 SUM1 1) 1 SUM2 -1)
				 (DP=INT.SUM.ADD.SUM (DP=INT.SUM.ADD.SUM (LIST (CONS NIL -1)) 1 SUM1 -1) 1 SUM2 1)
				 CONDITION TAF GLOBAL.GTERM 'DISJUNCTION)))))


(DEFUN DB=INT.SUM.INSERT (SUM CONDITION TAF GLOBAL.GTERM &optional (TYPE 'INEQUALITY))

  ;;; Input:   a sum, a taf-access-function to a literal denoting the sum and the top-level gterm
  ;;; Effect:  inserts the inequality for each non-variable factor of sum into the database.
  ;;; Value:   undefined

  (MAPC #'(LAMBDA (PROD.INT)
	    (cond ((da-function.is (da-term.symbol (car (car (car prod.int)))))
		   (DB=PREFUN.DATABASE.ADD (DA-TERM.SYMBOL (car (car (car prod.int)))) TYPE
					   (LIST (caar prod.int) PROD.INT SUM CONDITION GLOBAL.GTERM TAF)
					   NIL GLOBAL.GTERM))))
	 (dp=int.sum.max.products SUM)))


(DEFUN DB=INT.SUMS.INSERT (SUM1 SUM2 CONDITION TAF GLOBAL.GTERM &optional (TYPE 'INEQUALITY))

  ;;; Input:   a sum, a taf-access-function to a literal denoting the sum and the top-level gterm
  ;;; Effect:  inserts the inequality for each non-variable factor of sum into the database.
  ;;; Value:   undefined

  (MAPC #'(LAMBDA (PROD.INT)
	    (cond ((da-function.is (da-term.symbol (car (car (car prod.int)))))
		   (DB=PREFUN.DATABASE.ADD (DA-TERM.SYMBOL (car (car (car prod.int)))) TYPE
					   (LIST (caar prod.int) PROD.INT (list SUM1 SUM2) CONDITION GLOBAL.GTERM TAF)
					   NIL GLOBAL.GTERM))))
	(dp=int.sum.max.products SUM1)))


;;;;; top-level-modifiers:
;;;;; ====================


(DEFUN DB=GTERM.INSERT.DISMSET.MODIFIERS (INPUT VALUE CONDITION ORG.GTERM ORG.TAF)
  
  ;;; Function  : DB=GTERM.INSERT.DISMSET.MODIFIERS 
  ;;; Author    : SA
  ;;; Edited    : 28.01.1993
  ;;; Input     : the two terms of an equation or the two literals of an implication, the conditions
  ;;;             for the equation/implication and the main gterm, in which the equation/implication
  ;;;             occurs.
  ;;; Effect    : inserts modifiers of the 'DISMSET type; for this modifiers inserts the following
  ;;;             informations in the attribute-list of the modifier:
  ;;;             1. Under the Property 'TYPES:
  ;;;                a. 'DISMSET, iff the disagreement multiset of the modifier isn't empty.
  ;;;                             Prefun-MSET(input)/Prefun-MSET(value) =/= NIL
  ;;;                             OR
  ;;;                             Variables-MSET(input)/Variables-MSET(value) =/= NIL
  ;;;                b. 'DISSET,  iff the disagreement set of the modifier isn't empty.
  ;;;                             Prefun(input)/Prefun(value) =/= NIL
  ;;;                             OR
  ;;;                             Variables(input)/Variables(value) =/= NIL
  ;;;                c. 'ELIMINATE, iff some *functions* (no predicates) of the disagreement set of
  ;;;                             the modifier are independent for the function symbols of the value.
  ;;;                             A =/= NIL   AND   some f of A is independent for Functions(value)
  ;;;                             (A = Functions(input)/Functions(value))
  ;;;             2. Under the property 'GENERATED.PREFUNS: a list of all generated function-symbols of
  ;;;                modifier, i.e.  Functions(value)/Functions(input)
  ;;;             3. Under the property 'GENERATED.SORTS: a list of the sorts, corresponding to variables of
  ;;;                this sorts, which are generated by the modifier, i.e. the sorts of the variables of
  ;;;                Variables(value)/Variables(input)
  ;;;             4. Under the property 'DISSET.FUNC the list Functions(input)/Functions(value)
  ;;;             5. Under the property 'DISSET.SORTS the list Variables(input)/Variables(value)
  ;;;             6. Under the property 'ELIMINATE the list of all f of A, which are independent for the
  ;;;                function-symbols Functions(value) (A = Functions(input)/Functions(value)). The list
  ;;;                of the eliminated functions is on under the property 'ELIMINATED.FUNCTIONS
  ;;; Value     : undef.

  (LET ((INPUT.PREFUN  (append (DA-GTERM.FUNCTIONS INPUT) (da-gterm.predicates input)))
	(INPUT.VARS    (DA-GTERM.VARIABLES INPUT))
	(Value.PREFUN  (append (DA-GTERM.FUNCTIONS VALUE) (da-gterm.predicates value)))
	(VALUE.VARS    (DA-GTERM.VARIABLES VALUE))
	DISMSET.PREFUN   DISMSET.SORTS
	DISSET.PREFUN    DISSET.SORTS
	GENERATED.PREFUN GENERATED.SORTS
	ELIMINATE.PREFUN
	ATTRIBUTES)
       
    (SETQ DISMSET.PREFUN (DA-SYMBOL.MULTISET.DIFFERENCE (APPEND (DA-GTERM.FUNCTIONS.MULTISET INPUT)
								(DA-GTERM.PREDICATES.MULTISET INPUT))
							(APPEND (DA-GTERM.FUNCTIONS.MULTISET VALUE)
								(DA-GTERM.PREDICATES.MULTISET VALUE))
							T))
    (SETQ DISMSET.SORTS (MAPCAR #'(LAMBDA (VARIABLE) (DA-VARIABLE.SORT VARIABLE))
				(DA-SYMBOL.MULTISET.DIFFERENCE (DA-GTERM.VARIABLES.MULTISET INPUT)
							       (DA-GTERM.VARIABLES.MULTISET VALUE)
							       T)))
    ;;; ELIMINATING MULTIPLE OCCURRENCES OF SORTS:
    (SETQ DISMSET.SORTS (REMOVE-DUPLICATES DISMSET.SORTS))
    (SETQ DISSET.PREFUN  (SET-DIFFERENCE INPUT.PREFUN VALUE.PREFUN))
    (SETQ DISSET.SORTS (MAPCAR #'(LAMBDA (VARIABLE) (DA-VARIABLE.SORT VARIABLE))
				  (SET-DIFFERENCE INPUT.VARS VALUE.VARS)))
    ;;; ELIMINATING MULTIPLE OCCURRENCES OF SORTS:
    (SETQ DISSET.SORTS (REMOVE-DUPLICATES DISSET.SORTS))
    (COND ((AND (DA-PREFUN.IS (DA-GTERM.SYMBOL INPUT))
		;(OR (DA-PREFUN.IS (DA-GTERM.SYMBOL VALUE))
		;    (DA-VARIABLE.IS (DA-GTERM.SYMBOL VALUE)))
		(OR DISMSET.PREFUN DISMSET.SORTS))
	   ;;; THE MODIFIER IS DISMSET ...
	   (SETQ GENERATED.PREFUN (SET-DIFFERENCE VALUE.PREFUN INPUT.PREFUN))
	   (SETQ GENERATED.SORTS (MAPCAR #'(LAMBDA (VARIABLE) (DA-VARIABLE.SORT VARIABLE))
					 (SET-DIFFERENCE VALUE.VARS INPUT.VARS)))
	   ;;; ELIMINATING MULTIPLE OCCURRENCES OF SORTS:
	   (REMOVE-DUPLICATES GENERATED.SORTS)
	   (SETQ ATTRIBUTES (NCONC (COND (GENERATED.PREFUN (LIST 'GENERATED.PREFUNS GENERATED.PREFUN)))
				   (COND (GENERATED.SORTS (LIST 'GENERATED.SORTS GENERATED.SORTS)))
				   (LIST 'TYPES (LIST 'DISMSET))))
	   (COND ((OR DISSET.PREFUN DISSET.SORTS)
		  ;;; THE MODIFIER IS DISSET ...
		  (SETF (GETF ATTRIBUTES 'TYPES) (CONS 'DISSET (GETF ATTRIBUTES 'TYPES)))
		  (SETQ ATTRIBUTES
			(NCONC ATTRIBUTES
			       (COND (DISSET.PREFUN (LIST 'DISSET.PREFUN DISSET.PREFUN)))
			       (COND (DISSET.SORTS (LIST 'DISSET.SORTS DISSET.SORTS)))))
		  (COND ((SETQ ELIMINATE.PREFUN (MAPCAN #'(LAMBDA (FUNC)
							  (AND (da-function.is func)
							       (DA-PREFUN.IS.INDEPENDENT FUNC VALUE.PREFUN)
							       (LIST FUNC)))
						      DISSET.PREFUN))
			 ;;; MODIFIER IS ELIMINATING FOR THE FUNCTIONS IN ``ELIMINATE.PREFUN''...
			 (SETF (GETF ATTRIBUTES 'TYPES) (CONS 'ELIMINATE (GETF ATTRIBUTES 'TYPES)))
			 (NCONC ATTRIBUTES
				(LIST 'ELIMINATED.FUNCTIONS ELIMINATE.PREFUN))))))
	   ;;; INSERTING MODIFIERS:
	   (MAPC #'(LAMBDA (FUNC)
		     (DB=MODIFIER.INSERT (DA-ACCESS (CAR (DA-SYMBOL.OCCURS.IN.GTERM FUNC INPUT)) INPUT)
					 'DISMSET INPUT VALUE NIL CONDITION ORG.GTERM org.taf ATTRIBUTES))
		 DISMSET.PREFUN)
	   (MAPC #'(LAMBDA (SORT)
		     (DB=MODIFIER.INSERT SORT 'DISMSET INPUT VALUE NIL CONDITION ORG.GTERM org.taf ATTRIBUTES))
		 DISMSET.SORTS)))))


(DEFUN DB=MODIFIER.RECURSIVE.CHANGES (INPUT VALUE TAFS)
  
  ;;; Author    : SA
  ;;; Edited    : 28.01.1994
  ;;; Arguments : two gterms and a list of tafs, denoting subterms if the second gterm.
  ;;; Effect    : /
  ;;; Value     : 

  (MAPCAR #'(LAMBDA (TAF)
	      (LIST TAF (db=gterm.compute.permutations INPUT (DA-ACCESS TAF VALUE) T NIL NIL)))
	  TAFS))


(defun db=gterm.compute.permutations (gterm1 gterm2 &optional variable normal.constants skolem.constants)
  
  ;;; Edited    : 
  ;;; Input     : 
  ;;; Effect    : 
  ;;; Value     : 
  ;;; Note      : replaces the function DB=POSITION.CHANGES.BETWEEN.GTERMS

  (append (cond (variable         (mapcan #'(lambda (variable)
					      (db=gterm.symbol.permutations gterm1 gterm2 variable))
					  (da-gterm.variables gterm1))))
	  (cond (normal.constants (mapcan #'(lambda (normal.constant)
					      (db=gterm.symbol.permutations gterm1 gterm2 normal.constant))
					  (da-gterm.constants gterm1 'noskolem))))
	  (cond (skolem.constants (mapcan #'(lambda (skolem.constant)
					      (db=gterm.symbol.permutations gterm1 gterm2 skolem.constant))
					  (da-gterm.constants gterm1 'skolem))))))


(defun db=gterm.symbol.permutations (gterm1 gterm2 symbol)
  
  ;;; Edited    : 
  ;;; Input     : 
  ;;; Effect    : 
  ;;; Value     : 
  ;;; Note      : both gterms must have the same top.level symbol

  (let ((input.tafs (da-symbol.occurs.in.gterm symbol gterm1))
	(value.tafs (da-symbol.occurs.in.gterm symbol gterm2)))
    (cond ((every #'(lambda (input.taf)
		      (every #'(lambda (value.taf)
				 (and (not (da-taf.are.equal input.taf value.taf))
				      (da-tafs.are.independent input.taf value.taf)))
			     value.tafs))
		  input.tafs)
	   (mapcar #'(lambda (input.taf)
		       (list symbol input.taf value.tafs))
		   input.tafs)))))


(DEFUN DB=GTERM.INSERT.VARIABLE.MODIFIERS (INPUT VALUE CONDITION ORG.GTERM org.taf)
  
  ;;; Author    : JCl
  ;;; Edited    : 25.02.1993
  ;;; Arguments : the two terms of an equation or the two literals of an implication, the conditions
  ;;;             for the equation/implication and the main gterm, in which the equation/implication
  ;;;             occurs.
  ;;; Effect    : inserts the modifier of the 'VARIABLE type if INPUT is a variable
  ;;; Value     : undef.

  (cond ((da-variable.is (da-gterm.symbol input))
	 (DB=MODIFIER.INSERT (DA-VARIABLE.SORT (da-gterm.symbol input)) 'VARIABLE INPUT VALUE NIL CONDITION 
			     ORG.GTERM org.taf))))


(DEFUN DB=GTERM.INSERT.RECURSIVE.MODIFIERS (INPUT VALUE CONDITION ORG.GTERM ORG.TAF TYPE)
  
  ;;; Function  : DB=GTERM.INSERT.RECURSIVE.MODIFIERS
  ;;; Author    : SA
  ;;; Edited    : 28.01.1994
  ;;; Arguments : two terms of an equation, the conditions and the main gterm.
  ;;; Effect    : inserts modifiers s -> t, which have the following properties:
  ;;;              1. s = f(u) and
  ;;;                 a. f doesn't occur in u
  ;;;                 b. f is independent for all function-symbols of u
  ;;;              2. neither f occurs only one times in t
  ;;;                 nor there exists two subterms u1 = f(..) and u2 = f(+++) of t, which have
  ;;;                 independent TAFs in t.
  ;;; Value     : undef.

  (LET ((SYMBOL (DA-GTERM.SYMBOL INPUT)) TAFS ATTRIBUTES)
    (COND ((AND (DA-PREFUN.IS SYMBOL)
		(EQ TYPE 'AXIOM)
		(DA-PREFUN.IS.DECLARED SYMBOL))
	   (REC-DECL.DEFINITION.ANALYZE SYMBOL INPUT VALUE)))
    (COND ((AND (DA-FUNCTION.IS SYMBOL)
		(EQ 1 (LENGTH (DA-SYMBOL.OCCURS.IN.GTERM SYMBOL INPUT)))
		(DA-PREFUN.IS.INDEPENDENT SYMBOL (DELETE SYMBOL (DA-GTERM.FUNCTIONS INPUT) :COUNT 1))
		(SETQ TAFS (DA-SYMBOL.OCCURS.IN.GTERM SYMBOL VALUE))
		(DA-TAFS.SOME.ARE.INDEPENDENT TAFS))
  	   ;;; MODIFIER IS RECURSIVE...
	   (SETQ ATTRIBUTES (LIST 'CHANGES (DB=MODIFIER.RECURSIVE.CHANGES INPUT VALUE TAFS)))
	   (DB=MODIFIER.INSERT INPUT 'RECURSIVE INPUT VALUE NIL CONDITION ORG.GTERM ORG.TAF ATTRIBUTES))
	  ((and (da-predicate.is symbol)
		(EQ 1 (LENGTH (DA-SYMBOL.OCCURS.IN.GTERM SYMBOL INPUT)))
		(DA-PREFUN.IS.INDEPENDENT SYMBOL (DELETE SYMBOL (DA-GTERM.PREDICATES INPUT) :COUNT 1))
		(SETQ TAFS (DA-SYMBOL.OCCURS.IN.GTERM SYMBOL VALUE))
		(DA-TAFS.SOME.ARE.INDEPENDENT TAFS))
	   (SETQ ATTRIBUTES (LIST 'CHANGES (DB=MODIFIER.RECURSIVE.CHANGES INPUT VALUE TAFS)))
	   (DB=MODIFIER.INSERT INPUT 'RECURSIVE INPUT VALUE NIL CONDITION ORG.GTERM ORG.TAF ATTRIBUTES)))))


(DEFUN DB=GTERM.INSERT.CHANGING.MODIFIERS (INPUT VALUE CONDITION ORG.GTERM ORG.TAF &OPTIONAL ATTRIBUTES)
  
  ;;; Function  : DB=GTERM.INSERT.CHANGING.MODIFIERS
  ;;; Author    : SA
  ;;; Edited    : 28.10.1994
  ;;; Arguments : two gterms of an equation/implication, the condition of the equation/implication
  ;;;             and the main gterm, in which occurs the equation/implication.
  ;;; Effect    : inserts modifiers of the folowing kind: f(...) -> f(+++). Information about the position
  ;;;             changes of variables are written under the property 'changes in the attribut-list of the
  ;;;             modifier.
  ;;; Value     : undef.

  (COND ((AND (EQ (DA-GTERM.SYMBOL INPUT) (DA-GTERM.SYMBOL VALUE))
	      (NOT (DA-VARIABLE.IS (DA-GTERM.SYMBOL INPUT))))
	 (SETQ ATTRIBUTES (CONS 'CHANGES (CONS (db=gterm.compute.permutations INPUT VALUE T NIL NIL) ATTRIBUTES)))
	 (DB=MODIFIER.INSERT INPUT 'CHANGING INPUT VALUE NIL CONDITION ORG.GTERM ORG.TAF ATTRIBUTES))))


(DEFUN DB=GTERM.INSERT.TOP.LEVEL.MODIFIERS (INPUT VALUE CONDITION ORG.GTERM ORG.TAF)

  ;;; Function  : db=gterm.insert.top.level.modifiers
  ;;; Author    : SA
  ;;; Edited    : 17.12.1993
  ;;; Arguments : two gterms (of an equation or an implication), the condition and the top level gterm
  ;;; Effect    : inserts modifiers of type f(...) -> g(...)
  ;;; Value     : ?

  (LET ((SYMBOL1 (DA-GTERM.SYMBOL INPUT))
	(SYMBOL2 (DA-GTERM.SYMBOL VALUE)))
    (COND ((AND (DA-prefun.is symbol1)    ; (da-prefun.is symbol2)
		(NOT (EQ SYMBOL1 SYMBOL2)))
	   (DB=MODIFIER.INSERT  INPUT 'TOP.LEVEL INPUT VALUE NIL
				CONDITION ORG.GTERM ORG.TAF)))))


(DEFUN DB=GTERM.INSERT.SIMPL.MODIFIER (GTERM1 GTERM2 TAF CONDITION ORG.GTERM ORG.TAF TYPE)

  ;;; Input:  two gterms, a term-access-function denoting those subterms of GTERM1 and GTERM2
  ;;;         which contain all differences of both and a list of gterms.
  ;;; Effect: enters top-to-top MODIFIERs of 

  (LET ((SUB.TERM1 (DA-ACCESS taf GTERM1)) (SUB.TERM2 (DA-ACCESS taf GTERM2)) S1.symbols s2.symbols)
    (COND ((AND (DA-TERM.IS SUB.TERM1)
		(NULL CONDITION)
		(NOT (DA-VARIABLE.IS (DA-TERM.SYMBOL SUB.TERM1))))	   
	   (COND ((AND (DA-TERM.IS.CONSTRUCTOR.GROUND SUB.TERM2)
		       (NOT (DA-TERM.IS.CONSTRUCTOR.GROUND SUB.TERM1)))
		  (DB=MODIFIER.INSERT sub.term1 'SIMPLIFICATIONS GTERM1 GTERM2 TAF CONDITION 
				      ORG.GTERM ORG.TAF (LIST 'TYPE TYPE))))
	   (cond ((and (NULL (DA-GTERM.TERMLIST SUB.TERM1))
		       (DA-FUNCTION.IS (DA-TERM.SYMBOL SUB.TERM1))
		       (DA-FUNCTION.SKOLEM (DA-TERM.SYMBOL SUB.TERM1))
		       (null (da-gterm.variables sub.term2))
		       (not (da-gterm.occurs.in.gterm sub.term1 sub.term2))
		       (or (da-gterm.termlist sub.term2)
			   (not (DA-FUNCTION.SKOLEM (DA-TERM.SYMBOL SUB.TERM2)))
			   (string> (da-symbol.pname (DA-TERM.SYMBOL SUB.TERM2))
				    (da-symbol.pname (DA-TERM.SYMBOL SUB.TERM1)))))
		  (DB=MODIFIER.INSERT sub.term1 'SIMPLIFICATIONS GTERM1 GTERM2 TAF
					     CONDITION ORG.GTERM ORG.TAF (LIST 'TYPE TYPE)))
		 ((and (DA-TERM.IS.CONSTRUCTOR.GROUND SUB.TERM2)
		       (not (DA-TERM.IS.CONSTRUCTOR.GROUND SUB.TERM1)))
		  (DB=MODIFIER.INSERT sub.term1 'SIMPLIFICATIONS GTERM1 GTERM2 TAF
					     CONDITION ORG.GTERM ORG.TAF (LIST 'TYPE TYPE)))
		 ((not (da-gterm.occurs.in.gterm sub.term2 sub.term1))
		  (SETQ S1.symbols (DA-PREFUN.INDEPENDENT.SYMBOLS (DA-GTERM.PREFUNS SUB.TERM1)))
		  (SETQ s2.symbols (DA-PREFUN.INDEPENDENT.SYMBOLS (DA-GTERM.PREFUNS SUB.TERM2)))
		  (COND ((AND (SET-DIFFERENCE S1.symbols s2.symbols)
			      (SUBSETP (DA-GTERM.VARIABLES SUB.TERM2) (DA-GTERM.VARIABLES SUB.TERM1))
			      (SUBSETP (DA-GTERM.FUNCTIONS SUB.TERM2 'SKOLEM)
				       (DA-GTERM.FUNCTIONS SUB.TERM1 'SKOLEM))
			      (EVERY #'(LAMBDA (SYMBOL)
					 (NOT (DA-PREFUN.IS.INDEPENDENT SYMBOL S1.symbols)))
				     s2.symbols))
			 (DB=MODIFIER.INSERT sub.term1 'SIMPLIFICATIONS GTERM1 GTERM2 TAF
					     CONDITION ORG.GTERM ORG.TAF (LIST 'TYPE TYPE))))))))))



(DEFUN DB=GTERM.INSERT.ELIMINATE.MODIFIER (GTERM1 GTERM2 CONDITION ORG.GTERM ORG.TAF TYPE)

  (LET ((FCTS1 (DELETE-IF #'(LAMBDA (SYMBOL)
			      (OR (DA-FUNCTION.IS.CONSTRUCTOR SYMBOL)
				  (DA-FUNCTION.IS.SELECTOR SYMBOL)))
			  (DA-GTERM.FUNCTIONS GTERM1)))
	(FCTS2 (DELETE-IF #'(LAMBDA (SYMBOL)
			      (OR (DA-FUNCTION.IS.CONSTRUCTOR SYMBOL)
				  (DA-FUNCTION.IS.SELECTOR SYMBOL)))
			  (DA-GTERM.FUNCTIONS GTERM2)))
	TAFS)
    (MAPC #'(LAMBDA (FCT)
	      (COND ((DA-PREFUN.IS.INDEPENDENT FCT FCTS2)
		     (SETQ TAFS (DA-SYMBOL.OCCURS.IN.GTERM FCT GTERM1))
		     (DB=MODIFIER.INSERT (DA-ACCESS (CAR TAFS) GTERM1)
					 'ELIMINATE GTERM1 GTERM2 NIL CONDITION ORG.GTERM ORG.TAF
					 (LIST 'TAF TAFS 'TYPE TYPE)))))
	  (SET-DIFFERENCE FCTS1 FCTS2))))



;;;;; colour-modifiers:
;;;;; =================


(defun DB=GTERM.INSERT.COLOUR.MODIFIERS (GTERM1 GTERM2 CONDITION ORG.GTERM ORG.TAF TYPE both.directions)

  (LET (RESULT (SIMPLIFICATION T))
    (COND ((UNI-GTERM.ARE.EQUAL GTERM1 GTERM2) nil)
	  ((and (SETQ RESULT (UNI-GTERM.COLOURIZE GTERM1 GTERM2 'S+ 'IGNORE))
		(DA-GTERM.MAX.FADED.GTERMS GTERM2 (CAR RESULT)))
	   (mapc #'(lambda (solution)
		     (db=gterm.insert.cmodifier.insert gterm1 gterm2 solution CONDITION ORG.GTERM ORG.TAF TYPE)
		     (cond (both.directions
			    (db=gterm.insert.cmodifier.remove gterm2 gterm1 solution CONDITION ORG.GTERM ORG.TAF TYPE))))
		 (reverse result)))
	  ((setq result (UNI-GTERM.COLOURIZE GTERM1 GTERM2 'IGNORE 'S+))
	   (mapc #'(lambda (solution)
		     (db=gterm.insert.cmodifier.remove gterm1 gterm2 solution CONDITION ORG.GTERM ORG.TAF TYPE)
		     (cond (both.directions
			    (db=gterm.insert.cmodifier.insert gterm2 gterm1 solution CONDITION ORG.GTERM ORG.TAF TYPE))))
		 (reverse result)))
	  ((setq result (append (UNI-GTERM.COLOURIZE GTERM1 GTERM2 
						     (COND ((AND (DA-LITERAL.IS GTERM1) (DA-LITERAL.IS.EQUALITY GTERM1))
							    'S+C*S+)  ;;; changed from S++C*S+ because of f(x,y)=0 -> (x=0 and y=0)
							   (t 'S+C*S+))
						     'S*C*S+)
				(UNI-GTERM.COLOURIZE GTERM1 GTERM2 'C*S+ 'S+C*S+)))
	   (mapc #'(lambda (solution)
		     (setq simplification (db=gterm.insert.cmodifier.move gterm1 gterm2 solution CONDITION 
									  ORG.GTERM ORG.TAF TYPE simplification)))
		 (reverse result))
	   (cond (both.directions
		  (setq result (append (UNI-GTERM.COLOURIZE GTERM2 GTERM1
							    (COND ((AND (DA-LITERAL.IS GTERM2) 
									(DA-LITERAL.IS.EQUALITY GTERM2))
								   'S++C*S+)
								  (t 'S+C*S+))
							    'S*C*S+)
				       (UNI-GTERM.COLOURIZE GTERM2 GTERM1 'C*S+ 'S+C*S+)))
		  (mapc #'(lambda (solution)
			    (setq simplification (db=gterm.insert.cmodifier.move 
						  gterm2 gterm1 solution CONDITION ORG.GTERM ORG.TAF 
						  TYPE simplification)))
			(reverse result))))))))
    
	  
(DEFUN DB=GTERM.INSERT.CMODIFIER.insert (GTERM1 GTERM2 SOLUTION CONDITION ORG.GTERM ORG.TAF TYPE)
  
  ;;; Input : left, right: two coloured terms 
  ;;; Effect: classifies the equation to one of the following types,
  ;;;         and inserts it into the propertylist of a function symbol of equation
  ;;;         REMOVE or INSERT into the toplevel function symbol of the skeleton
  ;;; Value : undefined
  
  (MAPC #'(LAMBDA (COLOURED.TERM.TAF)
	    (COND ((NOT (DA-TAF.IS.TOP.LEVEL COLOURED.TERM.TAF GTERM2))
		   (DB=MODIFIER.INSERT (DA-ACCESS (CDR COLOURED.TERM.TAF) GTERM2)
				       'INSERT GTERM1 GTERM2
				       (DA-TAF.COLOUR.TAF COLOURED.TERM.TAF GTERM2 SOLUTION)
				       CONDITION ORG.GTERM ORG.TAF (LIST 'TYPE TYPE)
				       SOLUTION))))
	(DA-GTERM.MAX.COLOURED.GTERMS GTERM2 SOLUTION)))


(defun DB=GTERM.INSERT.CMODIFIER.remove (GTERM1 GTERM2 SOLUTION CONDITION ORG.GTERM ORG.TAF TYPE)

  (COND ((OR (DA-TERM.IS GTERM1) (DA-LITERAL.IS GTERM1))
	 (MAPC #'(LAMBDA (FADED.TERM.TAF)
		   (DB=MODIFIER.INSERT (DA-ACCESS FADED.TERM.TAF GTERM1)
				       'REMOVE GTERM1 GTERM2
				       FADED.TERM.TAF
				       CONDITION ORG.GTERM ORG.TAF (LIST 'TYPE TYPE)
				       SOLUTION))
	       (DA-GTERM.MAX.FADED.GTERMS GTERM1 SOLUTION))
	 (COND ((and (OR (DA-TERM.IS GTERM1)
			 (AND (DA-LITERAL.IS GTERM1)
			      (GETF (DA-GTERM.ATTRIBUTES GTERM1) 'EQV)))
		     (getf (da-gterm.attributes gterm1) :def.header))
		(DB=MODIFIER.INSERT GTERM1 'SIMPLIFICATIONS GTERM1 GTERM2 NIL CONDITION ORG.GTERM ORG.TAF))))))
 


(DEFUN DB=GTERM.INSERT.CMODIFIER.move (GTERM1 GTERM2 SOLUTION CONDITION ORG.GTERM ORG.TAF TYPE SIMPLIFICATION)

  ;;; Input:  a gterm, a term-access-function of LITERAL, denoting the gterm, a key, two list of term-
  ;;;         access-functions denoting the upper contexts of both sides of the equation and a taf denoting
  ;;;         the `left' side of the equation.
  ;;; Effect: computes the different context-moving c-equations caused by LITERAL and inserts them into the
  ;;;         database.
  ;;; Value:  T, if no simplification rule has been inserted, NIL otherwise.
  
  (LET* ((TAFS1 (DA-GTERM.MAX.FADED.GTERMS GTERM1 SOLUTION))
	 (TAFS2 (DA-GTERM.MAX.FADED.GTERMS GTERM2 SOLUTION))
	 TAF1 TAF2 INNER.CONTEXT.TAF COLOUR1.TAF CONTEXT.TAFS ARG.LIMITED)
    (COND ((AND (EQ (LENGTH TAFS1) 1) (EQ (length tafs2) 1)
		(CAR TAFS2) (null (CAR TAFS1))
		(OR (DA-TERM.IS GTERM1) (DA-LITERAL.IS GTERM1)))
	   (SETQ INNER.CONTEXT.TAF (DA-TAF.SUPER.TAF (CAR (DA-GTERM.COLOURFUL.TERMS GTERM1))))
	   (SETQ COLOUR1.TAF (CAR (DA-GTERM.COLOURFUL.TERMS (DA-ACCESS (CAR TAFS2) GTERM2)
							    SOLUTION (CAR TAFS2))))
	   (SETQ CONTEXT.TAFS (DA-COLOUR.OCCURS.IN.GTERM (DA-GTERM.COLOUR (DA-ACCESS COLOUR1.TAF GTERM2) SOLUTION)
							 (DA-ACCESS INNER.CONTEXT.TAF GTERM1)
							 SOLUTION))
	   (DB=MODIFIER.INSERT (DA-ACCESS INNER.CONTEXT.TAF GTERM1)
			       'MOVE.DOWN GTERM1 GTERM2
			       INNER.CONTEXT.TAF CONDITION ORG.GTERM ORG.TAF (LIST 'TYPE TYPE)
			       SOLUTION CONTEXT.TAFS)))
    (COND ((AND (NOT (SOME #'(LAMBDA (TAF1) (null TAF1)) TAFS1))
		(EQ (LENGTH TAFS2) 1) (null (CAR TAFS2)))
	   (COND ((AND (DA-TERM.IS GTERM2)
		       (DA-TAFS.SOME.ARE.INDEPENDENT TAFS1))
		  (SETQ ARG.LIMITED (DB=GTERM.CONTEXT.IS.ARG.LIMITED GTERM2 SOLUTION))))
	   (MAPC #'(LAMBDA (TAF1)
		     (DB=MODIFIER.INSERT (DA-ACCESS TAF1 GTERM1)
					 'MOVE.UP GTERM1 GTERM2
					 TAF1 CONDITION ORG.GTERM ORG.TAF 
					 (LIST 'TYPE TYPE 'ARG.LIMITED ARG.LIMITED 'TAFS TAFS1)
					 SOLUTION))
		 TAFS1)
	   (COND ((AND (OR (DA-TERM.IS GTERM1) (GETF (DA-GTERM.ATTRIBUTES GTERM1) 'EQV))
		       (NULL CONDITION) SIMPLIFICATION
		       (DA=GTERM.CONTEXT.IS.LESS GTERM2 SOLUTION (DA-GTERM.SYMBOL GTERM1)))
		  (SETQ SIMPLIFICATION NIL)
		  (DB=MODIFIER.INSERT GTERM1 'SIMPLIFICATIONS GTERM1 GTERM2
				      NIL CONDITION ORG.GTERM ORG.TAF (LIST 'TYPE TYPE) SOLUTION)))
	   (COND ((AND (OR (DA-TERM.IS GTERM2) (DA-LITERAL.IS GTERM2)))
		  (DB=MODIFIER.INSERT GTERM2 'TOP.MOVE.UP GTERM1 GTERM2
				      NIL CONDITION ORG.GTERM ORG.TAF (LIST 'TYPE TYPE) NIL))))
	  ((AND (EQ (da-taf.length tafs1) 1)
		(eq (da-taf.length tafs2) 1)
		(NOT (DA-TAF.ARE.EQUAL (SETQ TAF2 (CAR TAFS2)) NIL)) ;;; GTERM2: S+CS+
		(EQ (DA-TAF.LENGTH (CAR TAFS1)) (DA-TAF.LENGTH (SETQ TAF2 (CAR TAFS2))))   ;; kann entfallen
		(DA-TAF.ARE.EQUAL (DA-TAF.SUPER.TAF TAF1) (DA-TAF.SUPER.TAF TAF2)))        ;; muessen nur unabhaengig sein !!
	   (DB=MODIFIER.INSERT (DA-ACCESS (CAR TAFS1) GTERM1)
			       'MOVE.ASIDE GTERM1 GTERM2
			       (CAR TAFS1) CONDITION ORG.GTERM ORG.TAF (LIST 'TYPE TYPE) SOLUTION
			       TAFS2)))
    SIMPLIFICATION))


(DEFUN DB=GTERM.CONTEXT.IS.ARG.LIMITED (GTERM SOLUTION)

  ;;; Input:  a coloured gterm and an indicator for the colouring
  ;;; Effect: analysis whether the top level context is argument-bounded. In case it is
  ;;;         the difference equivalent of this part of the formula is computed and
  ;;;         represented as a (distributive) list of literals
  ;;; Value:  a list of literal-lists dnoting the different difference-equivalences.

  (LET ((ACT.GTERM GTERM))
    (MAPCAN #'(LAMBDA (TAF)
		(setq ACT.GTERM GTERM)
		(COND ((EVERY #'(LAMBDA (ARG)
				  (prog1 (ASSOC ARG (DA-FUNCTION.ARG.LIMITED (DA-GTERM.SYMBOL ACT.GTERM)))
				    (SETQ ACT.GTERM (NTH (1- ARG) (DA-GTERM.TERMLIST ACT.GTERM)))))
			      (REVERSE TAF))
		       (SETQ ACT.GTERM GTERM)
		       (LIST (MAPCAR #'(LAMBDA (ARG)
					 (DA-LITERAL.CREATE (DA-SIGN.PLUS)
							    (SECOND (ASSOC ARG (DA-FUNCTION.ARG.LIMITED 
										(DA-GTERM.SYMBOL ACT.GTERM))))
							    (MAPCAR #'DA-TERM.COPY (DA-GTERM.TERMLIST ACT.GTERM))))
				     (REVERSE TAF))))))
	    (DA-GTERM.MAX.COLOURED.GTERMS GTERM SOLUTION))))
	       



;;;;; functions to insert/remove MODIFIERs.


(DEFUN DB-MODIFIER.SELECTION (GTERM TYPE SAME.SIGN BODY)

  ;;; Input:  a gterm, an atom, a sign and a functional
  ;;; Effect: searches the first modifier of type \verb$TYPE$ for the prefun of \verb$GTERM$
  ;;;         which satisfies \verb$BODY$
  ;;; Value:  the result of applying the modifier to \verb$BODY$
  
  (SOME #'(LAMBDA (MODIFIER)
	    (COND ((ded-input.is.active (da-modifier.defining.input modifier))
		   (FUNCALL BODY MODIFIER))))
	(DB=MODIFIER.SELECT GTERM TYPE SAME.SIGN)))


(DEFUN DB-MODIFIER.COLLECTION (GTERM TYPE SAME.SIGN BODY)

  ;;; Input:  a gterm, an atom, a sign and a functional
  ;;; Effect: searches for all modifiers of type \verb$TYPE$ for the prefun of \verb$GTERM$
  ;;;         which satisfy \v rb$BODY$
  ;;; Value:  the concatenation of all results of applying the modifiers to \verb$BODY$
  
  (MAPCAN #'(LAMBDA (MODIFIER)
	      (COND ((ded-input.is.active (da-modifier.defining.input modifier))
		     (FUNCALL BODY MODIFIER))))
	  (DB=MODIFIER.SELECT GTERM TYPE SAME.SIGN)))


(DEFUN DB=MODIFIER.SELECT (GTERM TYPE &OPTIONAL SAME.SIGN)

  ;;; Input:   a gterm, an atom and a sign
  ;;; Effect:  see value
  ;;; Value:   return the actual modifiers of type for the prefun of GTERM
  ;;;          In case gterm is a literal the input of modifier have different
  ;;;          opposite sign unless same.sign is specified.

  (COND ((DA-TERM.IS GTERM)
	 (COND ((EQ TYPE 'VARIABLE) (getf (da-sort.modifiers (DA-TERM.SORT GTERM)) 'VARIABLE))
	       ((da-variable.is (da-term.symbol gterm)) nil)
	       ((MEMBER TYPE '(DISSET ELIMINATE))
		(REMOVE-IF #'(LAMBDA (MODIFIER)
			       (NOT (MEMBER TYPE (GETF (DA-MODIFIER.ATTRIBUTES MODIFIER) 'TYPES))))
			   (GETF (DA-PREFUN.MODIFIERS (DA-TERM.SYMBOL GTERM)) 'DISMSET)))
	       (T (GETF (DA-PREFUN.MODIFIERS (DA-TERM.SYMBOL GTERM)) TYPE))))
	((DA-LITERAL.IS GTERM)
	 (GETF (GETF (DA-PREFUN.MODIFIERS (DA-LITERAL.SYMBOL GTERM))
		     (COND (SAME.SIGN (DA-LITERAL.SIGN GTERM))
			   (T (DA-SIGN.OTHER.SIGN (DA-LITERAL.SIGN GTERM)))))
	       TYPE))))


(DEFUN DB=MODIFIER.INSERT (GTERM TYPE INPUT VALUE INPUT.TAF CONDITION ORG.GTERM org.taf &OPTIONAL ATTRIBUTES &REST REST)

  ;;; Input:   an atom, a key for the database, two gterms a taf and a gterm
  ;;; Effect:  enters the denoted MODIFIER into the given database and updates the history informations
  ;;; Value:   undefined.

  (LET* ((ENTRY (ASSOC ORG.TAF (GETF (DA-GTERM.ATTRIBUTES ORG.GTERM) 'MODIFIERS) :TEST 'EQUAL))
	 (PNAME (FORMAT NIL "~A:[~{~D~}]" (DA-GTERM.PNAME ORG.GTERM) (REVERSE ORG.TAF)))
	 MODIFIER key)
    (COND ((NULL ENTRY)
	   (SETQ ENTRY (LIST ORG.TAF
			     (MAKE-DA*MODFRAME :INPUT INPUT :VALUE VALUE :CONDITION CONDITION
					       :PNAME PNAME :GTERM ORG.GTERM :TAF ORG.TAF)
			     NIL))
	   (PUSH ENTRY (GETF (DA-GTERM.ATTRIBUTES ORG.GTERM) 'MODFRAMES))))
    (SETQ MODIFIER (COND ((MEMBER TYPE '(MOVE.UP MOVE.DOWN MOVE.ASIDE INSERT REMOVE))
			  (MAKE-DA*COLOURED.MODIFIER
			   :INPUT.TAF INPUT.TAF :MODFRAME (second entry)
			   :SOLUTION (CAR REST) :VALUE.TAF (SECOND REST)
			   :ATTRIBUTES (cons 'environment (cons 'global ATTRIBUTES))))
			 (T (MAKE-DA*MODIFIER :MODFRAME (second entry) :INPUT.TAF INPUT.TAF 
					      :ATTRIBUTES (cons 'environment (cons 'global ATTRIBUTES))))))
    (COND ((DA-SORT.IS GTERM)
	   (setq key gterm)
	   (PUSH MODIFIER (GETF (DA-SORT.MODIFIERS KEY) TYPE)))
	  ((DA-TERM.IS GTERM)
	   (SETQ KEY (DA-TERM.SYMBOL GTERM))
	   (COND ((EQ TYPE 'INSERT) (SETF (GETF (DA-PREFUN.MODIFIERS KEY) TYPE) 
					  (MERGE 'LIST (LIST MODIFIER) (GETF (DA-PREFUN.MODIFIERS KEY) TYPE)
						 #'(LAMBDA (M1 M2) (> (LENGTH (DA-CMODIFIER.INPUT.TAF M1))
								      (LENGTH (DA-CMODIFIER.INPUT.TAF M2)))))))
		 (T (PUSH MODIFIER (GETF (DA-PREFUN.MODIFIERS KEY) TYPE)))))
	  ((DA-LITERAL.IS GTERM) ; war: T
	   (SETQ KEY (CONS (DA-GTERM.SYMBOL GTERM) (DA-LITERAL.SIGN GTERM)))
	   (PUSH MODIFIER (GETF (GETF (DA-PREFUN.MODIFIERS (CAR KEY)) (CDR KEY)) TYPE))))

   (PUSH (LIST MODIFIER key TYPE) (third entry))))


(DEFUN DB=MODIFIER.REMOVE.ALL (GTERM)

  (MAPC #'(LAMBDA (ENTRY)
	    (MAPC #'(LAMBDA (MODIFIER.KEY)
		      (DB=MODIFIER.REMOVE (CAR MODIFIER.KEY) (SECOND MODIFIER.KEY) (THIRD MODIFIER.KEY)))
		  (THIRD ENTRY)))
	(GETF (DA-GTERM.ATTRIBUTES GTERM) 'MODFRAMES))
  (SETF (GETF (DA-GTERM.ATTRIBUTES GTERM) 'MODFRAMES) NIL))


(DEFUN DB=MODIFIER.REMOVE (MODIFIER KEY TYPE)

  ;;; Input:   an atom, a key for the database and a MODIFIER
  ;;; Effect:  deletes destructively the MODIFIER from the specified database-list.

  (COND ((CONSP KEY)
	 (SETF (GETF (GETF (DA-PREFUN.MODIFIERS (CAR KEY)) (CDR KEY)) TYPE)
	       (DELETE MODIFIER (GETF (GETF (DA-PREFUN.MODIFIERS (CAR KEY)) (CDR KEY)) TYPE) :COUNT 1)))
	(T (cond ((da-sort.is key)
		  (SETF (GETF (DA-SORT.MODIFIERS KEY) TYPE)
		       (DELETE MODIFIER (GETF (DA-SORT.MODIFIERS KEY) TYPE) :COUNT 1)))
		 (T
		  (SETF (GETF (DA-PREFUN.MODIFIERS KEY) TYPE)
			(DELETE MODIFIER (GETF (DA-PREFUN.MODIFIERS KEY) TYPE) :COUNT 1))))))
  (MAPC #'(LAMBDA (HISTORY) (EVAL HISTORY)) (GETF (DA-MODIFIER.ATTRIBUTES MODIFIER) 'HISTORY))
  (setf (GETF (DA-MODIFIER.ATTRIBUTES MODIFIER) 'HISTORY) nil))


(DEFUN DB=TAFS.OF.OCCURENCES.OF.VARIABLE (VARIABLE LISTE)

  ;;; Function  : db=tafs.of.occurences.of.variable
  ;;; Author    : SA
  ;;; Edited    : 20.12.1993
  ;;; Arguments : a variable and a list resulting from the function da-gterm.removed.variables, i.e.
  ;;;             a list  ( ((1) (x))  ((2) (y)) )
  ;;; Effect    : /
  ;;; Value     : returns a list of these tafs corresponding to a varaible list which contains the
  ;;;             variable. 
  ;;;             Example: given the variable x and the list  ( ((1) (x))  ((2) (y)) ), the function
  ;;;             returns the list ((1)).
  
  (MAPCAN #'(LAMBDA (S.LISTE)
	      (COND ((MEMBER VARIABLE (CADR S.LISTE) :test #'equalp)
		     (LIST (CAR S.LISTE)))))
	  LISTE))


(DEFUN DB=POSITION.CHANGE (VARIABLE TAF LISTE1)

  ;;; Function  : db=position.change
  ;;; Author    : SA
  ;;; Edited    : 20.12.1993
  ;;; Arguments : a variable, a taf and a list resulting from the function da-gterm.removed.variables
  ;;; Effect    : /
  ;;; Value     : a list ( variable taf A ), where A is a list resulting from the function
  ;;;             db=tafs.of.occurences.of.variable called with variable and the given list liste1. 
  
  (LIST VARIABLE TAF (DB=TAFS.OF.OCCURENCES.OF.VARIABLE VARIABLE LISTE1)))


(DEFUN DB=POSITION.CHANGES (VARIABLES TAF LISTE1)

  ;;; Function  : db=position.changes
  ;;; Author    : SA
  ;;; Edited    : 20.12.1993
  ;;; Arguments : 
  ;;; Effect    : 
  ;;; Value     : removes all triple of the list, which corresponds to a variable which is removed.
  ;;;             I.e. all triples (u (2) NIL) are removed. The result is a list of all triples
  ;;;             corresponding to variables, which changes positions (between the two gterms).
  ;;;             See also db=position.changes.between.gterms.

  (MAPCAR #'(LAMBDA (VARIABLE)
	      (DB=POSITION.CHANGE VARIABLE TAF LISTE1))
	  VARIABLES))


(DEFUN DB=POSITION.CHANGES.BETWEEN.GTERMS (GTERM1 GTERM2
					   &OPTIONAL VARIABLES FUNCTIONS
					   SKOLEM.FUNCTIONS CONSTANTS SKOLEM.CONSTANTS)

  ;;; Function  : db=position.changes.between.gterms
  ;;; Author    : SA
  ;;; Edited    : 26.01.1994
  ;;; Arguments : two gterms
  ;;; Effect    : calculates the position changings of variables between gterm1 and gterm2
  ;;; Value     : a list ((var1 top_level_taf_of_var1_in_gterm1
  ;;;                           (1-top_level_taf_of_var1_in_gterm2 ... M1-top_level_taf_of_var1_in_gterm2))
  ;;;                     (varn top_level_taf_of_varn_in_gterm1
  ;;;                           (1-top_level_taf_of_varn_in_gterm2 ... Mn-top_level_taf_of_varn_in_gterm2)))
  ;;;             Example: given the gterms f(x, g(h(y,u)), z) and f(y, h(x,g(z)), x) then the result will
  ;;;                      be the following list:
  ;;;                      ( (x (1) ((2) (3)))    <--- this means that x in the gterm on taf (1) is
  ;;;                                                  moved in a the gterms on taf (2) and (3).
  ;;;                        (y (2) ((1)))
  ;;;                        (u (2) NIL)          <--- this means, that the u in the gterm on taf
  ;;;                                                  (2) is removed from the gterm.
  ;;;                        (z (3) (2)) )
  
  (LET ((REMOVED.SYMBOLS (DA-GTERM.REMOVED.SYMBOLS GTERM1 GTERM2
						       VARIABLES FUNCTIONS SKOLEM.FUNCTIONS
						       CONSTANTS SKOLEM.CONSTANTS))
	(INSERTED.SYMBOLS (DA-GTERM.REMOVED.SYMBOLS GTERM2 GTERM1
							VARIABLES FUNCTIONS SKOLEM.FUNCTIONS
							CONSTANTS SKOLEM.CONSTANTS)))
    (MAPCAN #'(LAMBDA (TAFXSYMBOLS)
		(DB=POSITION.CHANGES (CADR TAFXSYMBOLS)
				     (CAR TAFXSYMBOLS)
				     INSERTED.SYMBOLS))
	    REMOVED.SYMBOLS)))


;;;;;------------------------------------------------------------------------------------------------------
;;;;; ATTRIBUTES
;;;;;------------------------------------------------------------------------------------------------------

(DEFUN DB=GTERM.INSERT.ATTRIBUTES (GTERM)
  (LET (PRED FCT ATTR SIDE OTHER.SIDE)
       (COND ((AND (DA-LITERAL.IS GTERM)
		   (DA-LITERAL.IS.EQUATION GTERM))
	      (SETQ SIDE (DA-TAF.CREATE.LEFT) OTHER.SIDE (DA-TAF.CREATE.RIGHT))
	      (COND ((MULTIPLE-VALUE-SETQ (FCT ATTR)
					  (DA=ATTRIBUTE.FCT.COMMUTATIVE GTERM SIDE)))
		    ((MULTIPLE-VALUE-SETQ (FCT ATTR)
					  (DA=ATTRIBUTE.FCT.ASSOCIATIVE GTERM SIDE)))
		    ((MULTIPLE-VALUE-SETQ (FCT ATTR)
					  (DA=ATTRIBUTE.FCT.ASSOCIATIVE GTERM OTHER.SIDE)))
		    ((MULTIPLE-VALUE-SETQ (FCT ATTR)
					  (DA=ATTRIBUTE.FCT.NULL.OR.IDENTITY GTERM SIDE)))
		    ((MULTIPLE-VALUE-SETQ (FCT ATTR)
					  (DA=ATTRIBUTE.FCT.NULL.OR.IDENTITY GTERM OTHER.SIDE)))
		    ((MULTIPLE-VALUE-SETQ (FCT ATTR)
					  (DA=ATTRIBUTE.FCT.INVERSE GTERM SIDE)))
		    ((MULTIPLE-VALUE-SETQ (FCT ATTR)
					  (DA=ATTRIBUTE.FCT.INVERSE GTERM OTHER.SIDE))))
	      (COND (FCT (SETF (DA-ATTRIBUTE.DEFINING.INPUT ATTR) (GETF (DA-GTERM.ATTRIBUTES GTERM) 'DEFINING.INPUT))
			 (PUSH ATTR (GETF (DA-FUNCTION.ATTRIBUTES FCT) (DA-ATTRIBUTE.NAME ATTR)))
			 (PUSH #'(LAMBDA () (REMF (DA-FUNCTION.ATTRIBUTES FCT) (DA-ATTRIBUTE.NAME ATTR)))
			       (GETF (DA-GTERM.ATTRIBUTES GTERM) 'HISTORY)))))
	     ((AND (EQ (DA-GTERM.SYMBOL GTERM) 'OR)
		   (EVERY #'(LAMBDA (SG) (DA-LITERAL.IS SG)) (DA-GTERM.TERMLIST GTERM)))
	      (COND ((MULTIPLE-VALUE-SETQ (PRED ATTR)
					  (DA=ATTRIBUTE.PRED.REFLEXIVE (DA-GTERM.TERMLIST GTERM))))
		    ((MULTIPLE-VALUE-SETQ (PRED ATTR)
					  (DA=ATTRIBUTE.PRED.IRREFLEXIVE (DA-GTERM.TERMLIST GTERM))))
		    ((MULTIPLE-VALUE-SETQ (PRED ATTR)
					  (DA=ATTRIBUTE.PRED.SYMMETRIC (DA-GTERM.TERMLIST GTERM))))
		    ((MULTIPLE-VALUE-SETQ (PRED ATTR)
					  (DA=ATTRIBUTE.PRED.TRANSITIVE (DA-GTERM.TERMLIST GTERM)))))
	      (COND (PRED (SETF (DA-ATTRIBUTE.DEFINING.INPUT ATTR) (GETF (DA-GTERM.ATTRIBUTES GTERM) 'DEFINING.INPUT))
			  (PUSH ATTR (GETF (DA-PREDICATE.ATTRIBUTES PRED) (DA-ATTRIBUTE.NAME ATTR)))
			  (PUSH #'(LAMBDA () (REMF (DA-PREDICATE.ATTRIBUTES PRED) (DA-ATTRIBUTE.NAME ATTR)))
				(GETF (DA-GTERM.ATTRIBUTES GTERM) 'HISTORY))))))))

;;;;;
;;;;;**********************************************************************************************************
;;;;;
;;;;;  P R E D E F I N I T I O N S
;;;;;  ===========================
;;;;;
;;;;;**********************************************************************************************************


;;; Variable for the top-level sort

(DEFVAR DP*SORT.ANY NIL)

;;; Variable for the predicates =, TRUE and FALSE.

(DEFVAR DP*PREDICATE.EQUALITY NIL)
(DEFVAR DP*PREDICATE.TRUE NIL)
(DEFVAR DP*PREDICATE.FALSE NIL)

(DEFVAR DP*LITERAL.TRUE NIL)
(DEFVAR DP*LITERAL.FALSE NIL)


(DEFVAR DP*GTERM.EQ.REFLEXIVITY NIL)



(DEFUN DP-RESET ()
  
  ;;; Input:  none
  ;;; Effect: defines symbols like =, TRUE, FALSE
  ;;;         to an initial state.

  (DP=SORT.RESET)
  (DP=PREDICATE.RESET)                               ; create true- and false literal
  (DP=LITERAL.RESET)                                 ; create reflexivity GTERM x = x
  (DP=GTERM.RESET)
  (DP=INIT)
  )


(DEFMACRO DP-SORT.TOP.LEVEL.SORT ()
  ;;; Input: none
  ;;; Value: the top level sort ANY
  
  `DP*SORT.ANY)


(DEFMACRO DP-PREDICATE.EQUALITY ()
  ;;; Input: none
  ;;; Value: the predicate =
  
  `DP*PREDICATE.EQUALITY)


(DEFMACRO DP-PREDICATE.TRUE ()
  ;;; Input: none
  ;;; Value: the predicate denoting TRUE
  
  `DP*PREDICATE.TRUE)


(DEFMACRO DP-PREDICATE.FALSE ()
  ;;; Input: none
  ;;; Value: the predicate denoting FALSE
  
  `DP*PREDICATE.FALSE)


(DEFMACRO DP-LITERAL.TRUE ()
  ;;; Input: none
  ;;; Value: the literal denoting TRUE
  
  `DP*LITERAL.TRUE)


(DEFMACRO DP-LITERAL.FALSE ()
  ;;; Input: none
  ;;; Value: the literal denoting FALSE
  
  `DP*LITERAL.FALSE)


(DEFMACRO DP-GTERM.EQ.REFLEXIVITY ()
  ;;; Input: none
  ;;; Value: a literal denoting x = x where x is of sort ANY
  
  `DP*GTERM.EQ.REFLEXIVITY)


(DEFUN DP-TERM.IS.INT.NUMBER (TERM)
  
  ;;; edited : 10.02.93 by CS
  ;;; input  : a term
  ;;; value  : T or NIL, depending whether \verb$TERM$ denotes an int number 

  (LET ((SIMPL.TERM (EG-EVAL TERM)))
       (COND ((AND (EQ DP*SORT.INT (DA-SYMBOL.SORT (DA-TERM.SYMBOL SIMPL.TERM)))
		   (DA-TERM.IS.CONSTRUCTOR.GROUND SIMPL.TERM))
	      SIMPL.TERM))))


(DEFUN DP=SORT.RESET ()
  
  (SETQ DP*SORT.ANY (MAKE-DA*SORT :PNAME "any"))
  (SETF (DA-SORT.ALL.SUBSORTS DP*SORT.ANY) (LIST DP*SORT.ANY))
  (SETF (DA-SORT.ALL.SUPERSORTS DP*SORT.ANY) (LIST DP*SORT.ANY))
  (DB-SORT.INSERT DP*SORT.ANY))


(DEFUN DP=PREDICATE.RESET ()
  
  (SETQ DP*PREDICATE.TRUE (DA-PREDICATE.CREATE "True" NIL))
  (SETF (DA-PREDICATE.ATTRIBUTES DP*PREDICATE.TRUE) (LIST 'DEFINED T))
  (DB-PREDICATE.INSERT DP*PREDICATE.TRUE)
  (SETQ DP*PREDICATE.FALSE (DA-PREDICATE.CREATE "False" NIL))
  (SETF (DA-PREDICATE.ATTRIBUTES DP*PREDICATE.FALSE) (LIST 'DEFINED T))
  (DB-PREDICATE.INSERT DP*PREDICATE.FALSE)
  (SETQ DP*PREDICATE.EQUALITY (DA-PREDICATE.CREATE "=" (LIST DP*SORT.ANY DP*SORT.ANY)))
  (SETF (DA-PREDICATE.ATTRIBUTES DP*PREDICATE.EQUALITY) (LIST 'DEFINED T 'REFLEXIVE T 'SYMMETRIC T))
  (SETF (DA-PREDICATE.LISPFCT (DA-PREDICATE.EQUALITY)) 'EG-EQUAL)
  (DB-PREDICATE.INSERT DP*PREDICATE.EQUALITY))


(DEFUN DP-PREFUN.IS.PREDEFINED (SYMBOL)

  ;;; Input :  a symbol
  ;;; Value:   T, iff \verb$SYMBOL$ is predefined.

  (GETF (DA-PREFUN.ATTRIBUTES SYMBOL) 'PREDEFINED))


(DEFUN DP=LITERAL.RESET ()

  (SETQ DP*LITERAL.FALSE (DA-LITERAL.CREATE '+ DP*PREDICATE.FALSE NIL))
  (SETQ DP*LITERAL.TRUE (DA-LITERAL.CREATE '+ DP*PREDICATE.TRUE NIL)))


(DEFUN DP=GTERM.RESET ()

  (LET ((VAR (DA-VARIABLE.CREATE (DP-SORT.TOP.LEVEL.SORT))))
    (SETQ DP*GTERM.EQ.REFLEXIVITY (DA-LITERAL.CREATE (DA-SIGN.PLUS) DP*PREDICATE.EQUALITY
						     (LIST (DA-TERM.CREATE VAR) (DA-TERM.CREATE VAR))))
    (SETF (DA-GTERM.PNAME DP*GTERM.EQ.REFLEXIVITY) "Reflexivity of =")
    (DB-GTERM.INSERT DP*GTERM.EQ.REFLEXIVITY 'AXIOM)))



(DEFUN DP-LITERAL.IS.PREDEFINED (LITERAL)
  
  ;;; Edited : 17.04.94 by CS
  ;;; Input  : a literal
  ;;; Value  : T, iff literal denotes either an integer literal, a set literal, or
  ;;;          an array literal with predefined function and predicate symbols
  
  (OR (DP-INT.LITERAL.IS.PREDEFINED LITERAL)
      (DP-SET.LITERAL.IS.PREDEFINED LITERAL)
      (DP-ARRAY.LITERAL.IS.PREDEFINED LITERAL)))


(DEFUN DP-TERM.IS.PREDEFINED (TERM)
  
  ;;; Edited : 17.04.94 by CS
  ;;; Input  : a term
  ;;; Value  : T, iff term denotes either an integer term, a set term, or
  ;;;          an array term with predefined function symbols
  
  (OR (DP-INT.TERM.IS.PREDEFINED TERM)
      (DP-SET.TERM.IS.PREDEFINED TERM)
      (DP-ARRAY.TERM.IS.PREDEFINED TERM)))


(DEFUN DP-TERM.SIMPLIFY (TERM)
  
  ;;; Edited : 17.04.94 by CS
  ;;; Input  : a term (either an integer, a set , or an array term)
  ;;; Effect : tries to simplify the specified term depending
  ;;;          on its sort by calling a specific simplification routine
  
  (COND ((EQ (DA-TERM.SORT TERM) (DP-SORT.INT))
	 (DP-INT.SIMPLIFY.TERM TERM))
	((EQ (DA-TERM.SORT TERM) (DP-SORT.SET (DA-TERM.SORT TERM)))
	 (DP-SET.NORMALIZE.TERM TERM))
	((EQ (DA-TERM.SORT TERM) (DP-SORT.ARRAY (DA-TERM.SORT TERM)))
	 (DP-ARRAY.NORMALIZE.TERM TERM))
	(T TERM)))


(DEFUN DP-LITERAL.SIMPLIFY (LITERAL &OPTIONAL APPLY.FCT)
  
  ;;; Edited : 17.04.94 by CS
  ;;; Input  : a literal (either an integer, a set , or an array literal) and (optionally)
  ;;;          an apply function
  ;;; Effect : tries to simplify the specified literal depending
  ;;;          on its argument sorts by calling a specific simplification routine

  (COND ((DP-INT.LITERAL.IS.PREDEFINED LITERAL)
	 (DP-INT.LITERAL.SIMPLIFY LITERAL APPLY.FCT))
	((DP-SET.LITERAL.IS.PREDEFINED LITERAL)
	 (DP-SET.LITERAL.SIMPLIFY (DA-LITERAL.COPY LITERAL)))
	((DP-ARRAY.LITERAL.IS.PREDEFINED LITERAL)
	 (DP-ARRAY.LITERAL.SIMPLIFY (DA-LITERAL.COPY LITERAL)))
	(T LITERAL)))


;;;;;================================================================================================
;;;;;
;;;;; Definition of datatype INTEGER:
;;;;;
;;;;;================================================================================================


(DEFPARAMETER DP*INTEGER.INPUT
  
  (LIST '(("structure 0, s(p:nat):nat") nil)
	
	'(("structure +, -:sign") nil)
	
	'(("non-free structure make_int(sign:sign, abs:nat):int with"
	   "axiom all s1,s2:sign all n1,n2:nat "
	   "make_int(s1, n1) = make_int(s2, n2) eqv (n1 = n2 and (n1 = 0 or s1 = s2)) end")
	  nil)

	'(("all n:nat all s:sign abs(make_int(s, n)) = n")
	  (("all n:nat all s:sign abs(make_int(s, n)) = n")))

	'(("all n:nat all si:sign sign(make_int(si, s(p(n)))) = si")
	  (("all n:nat all si:sign sign(make_int(si, s(p(n)))) = si")))

	'(("all s:sign sign(make_int(s, 0)) = +")
	  (("all s:sign sign(make_int(s, 0)) = +")))

	'(("function null:int = make_int(+, 0)") nil)
	
	'(("function succ(x:int):int ="
	   "if abs(x) = 0 then make_int(+, s(0))"
	   "if abs(x) of s and sign(x) = + then make_int(+, s(abs(x)))"
	   "if abs(x) of s and sign(x) = - then make_int(-, p(abs(x)))") nil)
	
	'(("function pred(x:int):int ="
	   "if abs(x) = 0 then make_int(-, s(0))"
	   "if abs(x) of s and sign(x) = + then make_int(+, p(abs(x)))"
	   "if abs(x) of s and sign(x) = - then make_int(-, s(abs(x)))") nil)
	
	'(("function -(x:int):int ="
	   "if abs(x) = 0 then make_int(+, 0)"
	   "if abs(x) of s and sign(x) = + then make_int(-, abs(x))"
	   "if abs(x) of s and sign(x) = - then make_int(+, abs(x))") nil)
	
	'(("function +(x,y:int):int ="
	   "if abs(x) = 0 then y"
	   "if abs(x) of s and sign(x) = + then succ(+(make_int(+, p(abs(x))), y))"
	   "if abs(x) of s and sign(x) = - then pred(+(make_int(-, p(abs(x))), y))") nil)
	
	'(("function -(x,y:int):int = +(x, -(y))") nil)
	
	'(("function *(x,y:int):int ="
	   "if abs(x) = 0 then make_int(+, 0)"
	   "if abs(x) of s and sign(x) = + then +(*(make_int(+, p(abs(x))), y), y)"
	   "if abs(x) of s and sign(x) = - then +(*(make_int(-, p(abs(x))), y), -(y))") nil)

	'(("predicate <=(x,y:int) = "
	   "sign(+(y, -(x))) = +") nil)

	'(("lemma \"inverse succ,pred\": all x:int succ(pred(x)) = x")
	  (("all x:int succ(pred(x)) = x")))

	'(("lemma \"inverse pred,succ\": all x:int pred(succ(x)) = x")
	  (("all x:int pred(succ(x)) = x")))

	'(("lemma \"inverse of -\": all x:int -(-(x)) = x")
	  (("all x:int -(-(x)) = x")))

	'(("lemma \"commut. of +\": all x,y:int +(x, y) = +(y, x)")
	  (("all x,y:int +(x, y) = +(y, x)")))

	'(("lemma \"assoc. of +\": all x,y,z:int +(x, +(y, z)) = +(+(x, y), z)")
	  (("all x,y,z:int +(x, +(y, z)) = +(+(x, y), z)")))

	'(("lemma \"commut. of *\": all x,y:int *(x, y) = *(y, x)")
	  (("all x,y:int *(x, y) = *(y, x)")))

	'(("lemma \"assoc. of *\": all x,y,z:int *(x, *(y, z)) = *(*(x, y), z)")
	  (("all x,y,z:int *(x, *(y, z)) = *(*(x, y), z)")))

	'(("lemma \"distrib. of +,*\": all x,y,z:int *(+(x, y), z) = +(*(x, z), *(y, z))")
	  (("all x,y,z:int *(+(x, y), z) = +(*(x, z), *(y, z))")))

	'(("lemma \"inverse of +,-\": all x:int +(x, -(x)) = make_int(+, 0)")
	  (("all x:int +(x, -(x)) = make_int(+, 0)")))

	'(("predicate <(x,y:int) =  <=(succ(x), y)") nil)

	'(("predicate >=(x,y:int) =  <=(y, x)") nil)
	
	'(("predicate >(x,y:int) =  <=(succ(y), x)") nil)

	'(("function div(x,y:int):int ="
	   "if abs(y) = 0 then ?"
	   "if abs(y) of s and sign(y) = + then {"
	   "if abs(x) = 0 then make_int(+, 0)"
	   "if abs(x) of s and sign(x) = + then {"
	   "if <(x, y) then make_int(+, 0)"
	   "if not <(x, y) then succ(div(-(x, y), y)) }"
	   "if abs(x) of s and sign(x) = - then {"
	   "if <(-(x), y) then make_int(-, s(0))"
	   "if not <(-(x), y) then pred(div(+(x, y), y)) }}"
	   "if abs(y) of s and sign(y) = - then div(-(x), -(y))") nil)
 
	'(("function mod(x,y:int):int = "
	   "if abs(y) = 0 then ?"
	   "if abs(y) of s then -(x, *(div(x,y), y))") nil)
	  
	'(("lemma \"invsere of div,*\": all x,y,z:int not y = 0 impl div(*(x, y), y) = x")
	  (("all x,y,z:int not y = 0 impl div(*(x, y), y) = x")))

	'(("lemma \"Lemma mod,+\": all x,y,z:int not y = 0 impl  mod(+(*(x, y), z), y) = mod(z, y)")
	  (("all x,y,z:int not y = 0 impl  mod(+(*(x, y), z), y) = mod(z, y)")))))


;;;;;================================================================================================
;;;;;
;;;;; VARIABLES FOR THE  datatype INTEGER:
;;;;;
;;;;;================================================================================================

(DEFVAR DP*SORT.INT NIL)

(DEFVAR DP*PREDICATE.INT.LEQ NIL)
(DEFVAR DP*PREDICATE.INT.GEQ NIL)
(DEFVAR DP*PREDICATE.INT.LE NIL)
(DEFVAR DP*PREDICATE.INT.GE NIL)

(DEFVAR DP*FUNCTION.INT.MAKE_INT NIL)
(DEFVAR DP*FUNCTION.INT.NULL NIL)
(DEFVAR DP*FUNCTION.INT.SIGN NIL)
(DEFVAR DP*FUNCTION.INT.ABS NIL)
(DEFVAR DP*FUNCTION.INT.SUCC NIL)
(DEFVAR DP*FUNCTION.INT.PRED NIL)
(DEFVAR DP*FUNCTION.INT.PLUS NIL)
(DEFVAR DP*FUNCTION.INT.DIFF NIL)
(DEFVAR DP*FUNCTION.INT.NEG NIL)
(DEFVAR DP*FUNCTION.INT.DIV NIL)
(DEFVAR DP*FUNCTION.INT.MOD NIL)
(DEFVAR DP*FUNCTION.INT.MULT NIL)


(DEFVAR DP*SORT.SIGN NIL)
(DEFVAR DP*FUNCTION.SIGN.+ NIL)
(DEFVAR DP*FUNCTION.SIGN.- NIL)

(DEFVAR DP*SORT.NAT NIL)
(DEFVAR DP*FUNCTION.NAT.0 NIL)
(DEFVAR DP*FUNCTION.NAT.S NIL)
(DEFVAR DP*FUNCTION.NAT.P NIL)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;
;;;;;;;;;;;;;
;;;;;;;;;;;;; INTERFACE FUNCTIONS TO ACCESS THE PREDEFINED STRUCTURE INTEGER
;;;;;;;;;;;;;
;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(DEFMACRO DP-SORT.INT ()

  ;;; Value:  the sort \verb$INT$.
  
  `DP*SORT.INT)


(DEFMACRO DP-PREDICATE.INT.GEQ ()

  ;;; Value:  the predicate $>=$.

  `DP*PREDICATE.INT.GEQ)


(DEFMACRO DP-PREDICATE.INT.LEQ ()

  ;;; Value:  the predicate $<=$.
  
  `DP*PREDICATE.INT.LEQ)


(DEFMACRO DP-PREDICATE.INT.LE ()

  ;;; Value:  the predicate $<$.
  
  `DP*PREDICATE.INT.LE)


(DEFMACRO DP-PREDICATE.INT.GE ()

  ;;; Value:  the predicate $>$.
  
  `DP*PREDICATE.INT.GE)


(DEFMACRO DP-FUNCTION.INT.MAKE_INT ()

  ;;; Value:  the function \verb$make_int$.
  
  `DP*FUNCTION.INT.MAKE_INT)


(DEFMACRO DP-FUNCTION.INT.NULL ()

  ;;; Value:  the function \verb$null$.
  
  `DP*FUNCTION.INT.NULL)


(DEFMACRO DP-FUNCTION.INT.SIGN ()

  ;;; Value:  the sort \verb$SIGN$
  
  `DP*FUNCTION.INT.SIGN)


(DEFMACRO DP-FUNCTION.INT.ABS ()

  ;;; Value:  the function \verb$abs$.
  
  `DP*FUNCTION.INT.ABS)


(DEFMACRO DP-FUNCTION.INT.SUCC ()

  ;;; Value:  the function \verb$succ$.
  
  `DP*FUNCTION.INT.SUCC)


(DEFMACRO DP-FUNCTION.INT.PRED ()

  ;;; Value:  the function \verb$pred$.
  
  `DP*FUNCTION.INT.PRED)


(DEFMACRO DP-FUNCTION.INT.PLUS ()
 
  ;;; Value:  the function \verb$+$.
  
 `DP*FUNCTION.INT.PLUS)


(DEFMACRO DP-FUNCTION.INT.DIFF ()

  ;;; Value:  the function \verb$-$.
  
  `DP*FUNCTION.INT.DIFF)


(DEFMACRO DP-FUNCTION.INT.NEG ()

  ;;; Value:  the function \verb$neg$.
  
  `DP*FUNCTION.INT.NEG)


(DEFMACRO DP-FUNCTION.INT.DIV ()

  ;;; Value:  the function \verb$/$.
  
  `DP*FUNCTION.INT.DIV)


(DEFMACRO DP-FUNCTION.INT.MOD ()
 
  ;;; Value:  the function \verb$mod$.
  
 `DP*FUNCTION.INT.MOD)


(DEFMACRO DP-FUNCTION.INT.MULT ()

  ;;; Value:  the function \verb$*$.
  
  `DP*FUNCTION.INT.MULT)


(DEFMACRO DP-SORT.SIGN ()
 
  ;;; Value:  the sort \verb$SIGN$.
  
 `DP*SORT.SIGN)


(DEFMACRO DP-FUNCTION.SIGN.+ ()

  ;;; Value:  the function \verb$+$ on \verb$SIGN$.
  
  `DP*FUNCTION.SIGN.+)


(DEFMACRO DP-FUNCTION.SIGN.- ()

  ;;; Value:  the function \verb$-$ on \verb$SIGN$.
  
  `DP*FUNCTION.SIGN.-)


(DEFMACRO DP-SORT.NAT ()

  ;;; Value:  the sort \verb$nat$.
  
  `DP*SORT.NAT)


(DEFMACRO DP-FUNCTION.NAT.0 ()

  ;;; Value:  the function \verb$0$.
  
  `DP*FUNCTION.NAT.0)


(DEFMACRO DP-FUNCTION.NAT.S ()

  ;;; Value:  the function \verb$s$.
  
  `DP*FUNCTION.NAT.S)


(DEFMACRO DP-FUNCTION.NAT.P ()

  ;;; Value:  the function \verb$p$.
  
  `DP*FUNCTION.NAT.P)


(defun dp-int.term.is.predefined (term)

  ;;; Edited : 17.04.94 by CS
  ;;; Input  : an integer term
  ;;; Value  : T, iff the leading function symbol is a predefined integer function

  (let ((symbol (da-term.symbol term)))
    (or (eq symbol DP*FUNCTION.INT.MULT)
	(eq symbol DP*FUNCTION.INT.PLUS)
	(eq symbol DP*FUNCTION.INT.DIFF)
	(eq symbol DP*FUNCTION.INT.SUCC)
	(eq symbol DP*FUNCTION.INT.PRED)
	(eq symbol DP*FUNCTION.INT.NULL)
	(eq symbol DP*FUNCTION.INT.DIV))))


(defun dp-int.literal.is.predefined (literal)
  
  ;;; Edited : 17.04.94 by CS
  ;;; Input  : an integer literal
  ;;; Value  : T, iff the literal can be handled by the integer simplification routine

  (let ((symbol (da-literal.symbol literal)))
    (and (da-predicate.is.equality symbol)
	 (or (and (eq dp*sort.int (da-term.sort (car (da-literal.termlist literal))))
		  (eq dp*sort.int (da-term.sort (second (da-literal.termlist literal)))))
	     (and (eq (da-term.symbol (car (da-literal.termlist literal))) dp*function.int.sign)
		  (or (eq (da-term.symbol (second (da-literal.termlist literal))) dp*function.sign.+)
		      (eq (da-term.symbol (second (da-literal.termlist literal))) dp*function.sign.-)))))))
	
	


(DEFUN DP-INT.SIMPLIFY.TERM (TERM)

  ;;; Input :  an integer term
  ;;; Effect:  simplifies term according to the predefined integer functions $*, + , -,$ etc.
  ;;;          by integer normalization and factorization 
  ;;; Value :  the simplified term

  (DP=INT.SUM.TERM.CREATE (DP=INT.TERM.SUM.CREATE (DP-INT.TERM.NORMALIZE TERM))))


(DEFUN DP-INT.LITERAL.SIMPLIFY (LITERAL apply.function)

  ;;; Input :  a literal denoting an integer equation
  ;;; Effect:  simplifies literal according to the predefined integer functions $*, + , -,$ etc.
  ;;;          by normalization and inferences with the database
  ;;; Value :  a formula denoting the simplified literal

  (LET ((TERMLIST (DA-LITERAL.TERMLIST LITERAL)) SUMS FORMULA)
    (COND ((EQ (DA-TERM.SORT (CAR TERMLIST)) DP*SORT.INT)
	   (SETQ SUMS (DP=INT.SUM.EQUATION.CHECK
		       (DP=INT.SUM.FACTORIZE (DP=INT.SUM.ADD.SUM
					      (DP=INT.TERM.SUM.CREATE (DP-INT.TERM.NORMALIZE (CAR TERMLIST))) 1 
					      (DP=INT.TERM.SUM.CREATE (DP-INT.TERM.NORMALIZE (SECOND TERMLIST))) -1))))
	   (SETQ FORMULA (DA-FORMULA.JUNCTION.CLOSURE
			  'OR
			  (MAPCAR #'(LAMBDA (SUM)
				      (MULTIPLE-VALUE-BIND (LEFT RIGHT) (DP=INT.SUM.TERMS.CREATE SUM)
							   (DA-LITERAL.CREATE '+
									      (DA-PREDICATE.EQUALITY)
									      (LIST (DP=INT.TERM.CHECK LEFT) (DP=INT.TERM.CHECK RIGHT))
									      (DA-LITERAL.ATTRIBUTES LITERAL))))
				  SUMS)))
	   (COND ((DA-SIGN.IS.NEGATIVE (DA-LITERAL.SIGN LITERAL))
		  (SETQ FORMULA (DA-FORMULA.NEGATE FORMULA))))
	   (NORM-NORMALIZATION FORMULA))
	  (T (DP-INT.INEQUALITY.SIMPLIFY LITERAL APPLY.FUNCTION)))))


(DEFUN DP=INT.TERM.CHECK (GTERM)

  ;;; Input:  an integer or a gterm containig integers
  ;;; Effect: converts \verb$GTERM$ into a term where all integers are expanded to gterms like \verb$MAKE_INT(+,...)$
  ;;; Value:  the converted \verb$GTERM$

  (COND ((INTEGERP (DA-GTERM.SYMBOL GTERM))
	 (DP=INT.INTEGER.CREATE (DA-GTERM.SYMBOL GTERM)))
	(T (DA-TERM.CREATE (DA-GTERM.SYMBOL GTERM) (MAPCAR #'(LAMBDA (SUBTERM) (DP=INT.TERM.CHECK SUBTERM))
							   (DA-GTERM.TERMLIST GTERM))))))


(DEFUN DP-INT.INEQUALITY.SIMPLIFY (LITERAL APPLY.FUNCTION)

  ;;; Input : an integer inequality literal and a functional denoting a prover for formulas.
  ;;; Effect: simplifies the specified literal according to the integer-arithmetic
  ;;;         by normalization and inferences with the database
  ;;; Value : the simplified literal
  
  (LET ((VALUE (DA-TERM.SYMBOL (SECOND (DA-LITERAL.TERMLIST LITERAL))))
	(SIGN (DA-LITERAL.SIGN LITERAL)) SUM KIND)
    (SETQ KIND (COND ((AND (DA-SIGN.IS.NEGATIVE SIGN)
			   (EQ (DP-FUNCTION.SIGN.+) VALUE))
		      'NEGATED)
		     ((AND (DA-SIGN.IS.POSITIVE SIGN)
			   (EQ (DP-FUNCTION.SIGN.-) VALUE))
		      'NEGATED)
		     (T 'POSITIVE)))		 
    (SETQ SUM (DP=INT.TERM.SUM.CREATE
	       (DP-INT.TERM.NORMALIZE
		(CAR (DA-TERM.TERMLIST (CAR (DA-LITERAL.TERMLIST LITERAL)))))))
    (COND ((EQ KIND 'NEGATED)
	   (SETQ SUM (DP=INT.SUM.ADD.SUM SUM -1 (LIST (CONS NIL -1)) 1))))
    (COND ((EVERY #'(LAMBDA (SUM.LIST)
		      (DP=INT.REDUCE.SUM.LIST (CONS SUM SUM.LIST)))
		  (DP=INT.SUM.DATABASE.ENTRIES SUM APPLY.FUNCTION))
	   (DA-LITERAL.FALSE))
	  (T LITERAL))))


(DEFUN DP=INT.REDUCE.SUM.LIST (SUM.LIST)

  ;;; Input:  a list of sums
  ;;; Effect:  tries to eliminate all non-constant products of the sum lists by
  ;;;          multiplication and addition.
  ;;; Value:   t if sum.list is inconsistent
  
  (LET (RESULT ABORT)
    (WHILE (AND (NULL ABORT)
		(MULTIPLE-VALUE-SETQ (RESULT SUM.LIST)
		  (DP=INT.SUM.LIST.ELIMINATE.PRODUCT SUM.LIST)))
      (COND ((SOME #'(LAMBDA (SUM)
		       (AND SUM
			    (NULL (CDR SUM))
			    (NULL (CAR (CAR SUM)))
			    (< (CDR (CAR SUM)) 0)))
		   SUM.LIST)
	     (SETQ ABORT T))))
    (SOME #'(LAMBDA (SUM)
	      (AND SUM
		   (NULL (CDR SUM))
		   (NULL (CAR (CAR SUM)))
		   (< (CDR (CAR SUM)) 0)))
	  SUM.LIST)))


(DEFUN DP=INT.SUM.LIST.ELIMINATE.PRODUCT (SUM.LIST)

  ;;; Input:   a list of sums
  ;;; Effect:  tries to eliminate all non-constant products of the sum lists by
  ;;;          multiplication and addition.
  ;;; Value:   a multiple-value:  t if sum.list is inconsistent and a list of sums. 

  (LET ((PRODUCT (CAAAR SUM.LIST)) POS.SUMS NEG.SUMS IRRELEVANT.SUMS ENTRY INT1 INT2)
    (MAPC #'(LAMBDA (SUM)
	      (COND ((SETQ ENTRY (ASSOC PRODUCT SUM :TEST 'DP=INT.PRODUCT.ARE.EQUAL))
		     (COND ((< (CDR ENTRY) 0) (PUSH SUM NEG.SUMS))
			   (T (PUSH SUM POS.SUMS))))
		    (T (PUSH SUM IRRELEVANT.SUMS))))
	  SUM.LIST)
    (COND ((AND POS.SUMS NEG.SUMS)
	   (VALUES T (NCONC (MAPCAN #'(LAMBDA (POS.SUM)
					(SETQ INT1 (ABS (CDR (ASSOC PRODUCT POS.SUM :TEST 'DP=INT.PRODUCT.ARE.EQUAL))))
					(MAPCAR #'(LAMBDA (NEG.SUM)
						    (SETQ INT2 (ABS (CDR (ASSOC PRODUCT NEG.SUM :TEST 'DP=INT.PRODUCT.ARE.EQUAL))))
						    (DP=INT.SUM.ADD.SUM POS.SUM INT2 NEG.SUM INT1))
						NEG.SUMS))
				    POS.SUMS)
			    IRRELEVANT.SUMS)))
	  (T (VALUES NIL SUM.LIST)))))


(DEFUN DP-INT.TERM.NORMALIZE (TERM)

  ;;; Input:   a term
  ;;; Effect:  computes a kind of normal-form of term, where the simplification rules
  ;;;          are applied as specified below.
  ;;; Value:   the normalized term

  (LET ((SYMBOL (DA-TERM.SYMBOL TERM)) (TERMLIST (DA-TERM.TERMLIST TERM))
	SUB.SYMBOL SIGN)
    (COND ((EQ SYMBOL (DP-FUNCTION.INT.PLUS))
	   
	   ; RECURSION ON BOTH ARGUMENTS:
	   (SETQ TERM (DA-TERM.CREATE (DP-FUNCTION.INT.PLUS)
				      (MAPCAR #'(LAMBDA (SUBTERM)
						  (DP-INT.TERM.NORMALIZE SUBTERM))
					      TERMLIST))))
	  ((EQ SYMBOL (DP-FUNCTION.INT.DIFF))
	   
	   ; (A - B) = (A + (-B)):
	   (SETQ TERM (DA-TERM.CREATE (DP-FUNCTION.INT.PLUS)
				      (LIST (DP-INT.TERM.NORMALIZE (CAR TERMLIST))
					    (DP-INT.TERM.NORMALIZE (DA-TERM.CREATE (DP-FUNCTION.INT.NEG)
									       (LIST (SECOND TERMLIST))))))))

	  ((EQ SYMBOL (DP-FUNCTION.INT.NULL))

	   (SETQ TERM (DA-TERM.CREATE 0)))
	  
	  ((EQ SYMBOL (DP-FUNCTION.INT.NEG))
	   
	   (SETQ SUB.SYMBOL (DA-TERM.SYMBOL (CAR TERMLIST)))
	   (COND ((NUMBERP SUB.SYMBOL)
		  
		  ; INTEGER A
		  (SETQ TERM (DA-TERM.CREATE (- 0 SUB.SYMBOL))))

		 ((EQ SYMBOL (DP-FUNCTION.INT.NULL))

		  (SETQ TERM (DA-TERM.CREATE 0)))
		 
		 ((EQ SUB.SYMBOL (DP-FUNCTION.INT.NEG))
		  
		  ; -(-A)  = A
		  (SETQ TERM (DP-INT.TERM.NORMALIZE (CAR (DA-TERM.TERMLIST (CAR TERMLIST))))))
		 ((EQ SUB.SYMBOL (DP-FUNCTION.INT.MAKE_INT))

		  ; -(MAKE_INT(+/-, N)) = MAKE_INT(-/+, N)
		  (SETQ SIGN (DA-TERM.SYMBOL (CAR (DA-TERM.TERMLIST (CAR TERMLIST)))))
		  (COND ((OR (EQ SIGN (DP-FUNCTION.SIGN.+)) (EQ SIGN (DP-FUNCTION.SIGN.-)))
			 (SETQ TERM (DP-INT.TERM.NORMALIZE
				     (DA-TERM.CREATE SUB.SYMBOL
						     (LIST (DA-TERM.CREATE
							    (COND ((EQ SIGN (DP-FUNCTION.SIGN.+))
								   (DP-FUNCTION.SIGN.-))
								  (T (DP-FUNCTION.SIGN.+))))
							   (SECOND (DA-TERM.TERMLIST (CAR TERMLIST))))))))))
		 ((OR (EQ SUB.SYMBOL (DP-FUNCTION.INT.PLUS))
		      (EQ SUB.SYMBOL (DP-FUNCTION.INT.DIFF)))
		  
		  ; -(A +/- B) = (A +/- (-B))
		  (SETQ TERM (DP-INT.TERM.NORMALIZE
			      (DA-TERM.CREATE
			       SUB.SYMBOL
			       (LIST (DA-TERM.CREATE SYMBOL (LIST (CAR (DA-TERM.TERMLIST (CAR TERMLIST)))))
				     (DA-TERM.CREATE SYMBOL (LIST (SECOND (DA-TERM.TERMLIST (CAR TERMLIST))))))))))
		 ((EQ SUB.SYMBOL (DP-FUNCTION.INT.MULT))

		  ; -(A * B) = (-A) * B
		  (SETQ TERM (DP-INT.TERM.NORMALIZE
			      (DA-TERM.CREATE
			       SUB.SYMBOL
			       (LIST (DA-TERM.CREATE SYMBOL (LIST (CAR (DA-TERM.TERMLIST (CAR TERMLIST)))))
				     (SECOND (DA-TERM.TERMLIST (CAR TERMLIST))))))))
		 
		 ((EQ SUB.SYMBOL (DP-FUNCTION.INT.PRED))

		  ; -(PRED(A)) = (-A + 1)
		  (SETQ TERM (DA-TERM.CREATE (DP-FUNCTION.INT.PLUS)
					     (LIST (DA-TERM.CREATE 1)
						   (DP-INT.TERM.NORMALIZE
						    (DA-TERM.CREATE SYMBOL (LIST (CAR (DA-TERM.TERMLIST
										       (CAR TERMLIST))))))))))
		 ((EQ SUB.SYMBOL (DP-FUNCTION.INT.SUCC))

		  ;  -(SUCC(A)) = (-A + (-1))
		  (SETQ TERM (DA-TERM.CREATE (DP-FUNCTION.INT.PLUS)
					     (LIST (DA-TERM.CREATE -1)
						   (DP-INT.TERM.NORMALIZE
						    (DA-TERM.CREATE SYMBOL (LIST (CAR (DA-TERM.TERMLIST
										       (CAR TERMLIST))))))))))))
	  ((EQ SYMBOL (DP-FUNCTION.INT.MULT))

	   ; (A + B) * (C + D) = (A * C) + (A * D) + (B * C) + (B * D)
	   (SETQ TERMLIST (MAPCAR #'(LAMBDA (SUB.TERM) (DP-INT.TERM.NORMALIZE SUB.TERM)) TERMLIST))
	   (SETQ TERM (DP=INT.TERMLIST.MULTIPLY TERMLIST)))
	  ((EQ SYMBOL (DP-FUNCTION.INT.SUCC))
	   
	   ; SUCC(A) = A + 1
	   (SETQ TERM (DA-TERM.CREATE (DP-FUNCTION.INT.PLUS)
				      (LIST (DA-TERM.CREATE 1)
					    (DP-INT.TERM.NORMALIZE (CAR TERMLIST))))))
	  ((EQ SYMBOL (DP-FUNCTION.INT.PRED))

	   ; PRED(A) = A + (-1)
	   (SETQ TERM (DA-TERM.CREATE (DP-FUNCTION.INT.PLUS)
				      (LIST (DA-TERM.CREATE -1)
					    (DP-INT.TERM.NORMALIZE (CAR TERMLIST))))))
	  ((EQ SYMBOL (DP-FUNCTION.INT.MAKE_INT))
	   (COND ((OR (EQ (DA-TERM.SYMBOL (CAR TERMLIST)) (DP-FUNCTION.SIGN.+))
		      (EQ (DA-TERM.SYMBOL (CAR TERMLIST)) (DP-FUNCTION.SIGN.-)))
		  (MULTIPLE-VALUE-BIND (DEPTH SUB.TERM) (DP=INT.TERM.OPEN.S (SECOND TERMLIST))
		    (COND ((EQ (DA-TERM.SYMBOL (CAR TERMLIST)) (DP-FUNCTION.SIGN.-)) (SETQ DEPTH (- 0 DEPTH))))
		    (COND ((EQ (DA-TERM.SYMBOL SUB.TERM) (DP-FUNCTION.NAT.0)) (SETQ TERM (DA-TERM.CREATE DEPTH)))
			  ((> DEPTH 0) (SETQ TERM (DA-TERM.CREATE (DP-FUNCTION.INT.PLUS)
								  (LIST (DA-TERM.CREATE DEPTH) SUB.TERM)))))))))
	  (T (SETQ TERM (DA-TERM.CREATE (DA-TERM.SYMBOL TERM)
					(MAPCAR #'DP-INT.TERM.NORMALIZE (DA-TERM.TERMLIST TERM))))))
    TERM))



(DEFUN DP=INT.TERMLIST.MULTIPLY (TERMLIST)

  ;;; Input:   a (associative) function symbol and a list of two terms
  ;;; Effect:  let both terms be sums then the sum of all products of the terms of both sums
  ;;;          is computed
  ;;; Value:   the computed sum.

  (LET ((LEFT.ARGS (DA-TERM.FUNCTION.OPEN (CAR TERMLIST) (DP-FUNCTION.INT.PLUS)))
	(RIGHT.ARGS (DA-TERM.FUNCTION.OPEN (SECOND TERMLIST) (DP-FUNCTION.INT.PLUS))))
    (DA-TERM.FUNCTION.CLOSURE
     (DP-FUNCTION.INT.PLUS)
     (MAPCAN #'(LAMBDA (LEFT.ARG)
		 (MAPCAR #'(LAMBDA (RIGHT.ARG)
			     (DA-TERM.CREATE (DP-FUNCTION.INT.MULT) (LIST LEFT.ARG RIGHT.ARG)))
			 RIGHT.ARGS))
	     LEFT.ARGS)
     (DA-TERM.CREATE 0))))



(DEFUN DP=INT.TERM.OPEN.S (TERM)

  ;;; Input:  a term
  ;;; Effect: eliminates all preceeding function symbols $s$ (successor of nat).
  ;;; Value:  a multiple value: the number of leading $s$ and the computed subterm  

  (COND ((EQ (DA-TERM.SYMBOL TERM) (DP-FUNCTION.NAT.S))
	 (MULTIPLE-VALUE-BIND (DEPTH SUB.TERM) (DP=INT.TERM.OPEN.S (CAR (DA-TERM.TERMLIST TERM)))
	   (VALUES (1+ DEPTH) SUB.TERM)))
	(T (VALUES 0 TERM))))


(DEFUN DP=INT.TERM.SUM.CREATE (TERM)

  ;;; Input:   a term (denoting a sum)
  ;;; Effect:  computes the terms of the sum and sorts them according the non-integer factors
  ;;;          of the denoted products.
  ;;; Value:   a list of dotted pairs: product . integer-value.
  
  (LET (SUM PROD.INT)
    (MAPC #'(LAMBDA (SUBTERM)
	      (SETQ PROD.INT (DP=INT.TERM.FACTORIZE SUBTERM))
	      (SETQ SUM (DP=INT.SUM.ADD.TERM SUM (CDR PROD.INT) (DP=INT.PRODUCT.NORMALIZE (CAR PROD.INT)))))
	  (DA-TERM.FUNCTION.OPEN TERM (DP-FUNCTION.INT.PLUS)))
    (DP=INT.SUM.NORMALIZE (REMOVE-IF #'(LAMBDA (FAC.INT) (ZEROP (CDR FAC.INT))) SUM))))


(DEFUN DP=INT.TERM.FACTORIZE (TERM)

  ;;; Input:   a term
  ;;; Effect:  factorizes term into a constant integer (numbers) and a list of non-constant
  ;;;          integers
  ;;; Value    a multiple-value: the number and the list of non-constant integers
  
  (LET ((SYMBOL (DA-TERM.SYMBOL TERM)) LEFT RIGHT)
    (COND ((EQ SYMBOL (DP-FUNCTION.INT.NEG))
	   (COND ((INTEGERP (DA-TERM.SYMBOL (CAR (DA-TERM.TERMLIST TERM))))
		  (CONS NIL (- 0 (DA-TERM.SYMBOL (CAR (DA-TERM.TERMLIST TERM))))))
		 (T (CONS (LIST (CONS (CAR (DA-TERM.TERMLIST TERM)) 1)) -1))))
	  ((EQ SYMBOL (DP-FUNCTION.INT.MULT))
	   (SETQ LEFT (DP=INT.TERM.FACTORIZE (CAR (DA-TERM.TERMLIST TERM))))
	   (SETQ RIGHT (DP=INT.TERM.FACTORIZE (SECOND (DA-TERM.TERMLIST TERM))))
	   (CONS (NCONC (CAR LEFT) (CAR RIGHT)) (* (CDR LEFT) (CDR RIGHT))))
	  ((INTEGERP (DA-TERM.SYMBOL TERM))
	   (CONS NIL (DA-TERM.SYMBOL TERM)))
	  (T (CONS (LIST (CONS TERM 1)) 1)))))


(DEFUN DP=INT.SUM.TERM.CREATE (SUM)

  ;;; Input:   a sum (list of dotted pairs: product . integer-value)
  ;;; Effect:  converts \verb$SUM$ into a term.
  ;;; Value:   the corresponding term

  (LET (PRODUCT.TERM)
    (DA-TERM.FUNCTION.CLOSURE
     (DP-FUNCTION.INT.PLUS)
     (MAPCAR #'(LAMBDA (FAC.INT)
		 (SETQ PRODUCT.TERM (DP=INT.PRODUCT.TERM.CREATE (CAR FAC.INT)))
		 (COND ((EQ (CDR FAC.INT) 1) PRODUCT.TERM)
		       ((EQ (CDR FAC.INT) -1) (DA-TERM.CREATE DP*FUNCTION.INT.NEG (LIST PRODUCT.TERM)))
		       ((NULL (CAR FAC.INT)) (DP=INT.INTEGER.CREATE (CDR FAC.INT)))
		       ((> (CDR FAC.INT) 1)
			(DA-TERM.CREATE (DP-FUNCTION.INT.MULT) (LIST (DP=INT.INTEGER.CREATE (CDR FAC.INT)) PRODUCT.TERM)))
		       (T (DA-TERM.CREATE DP*FUNCTION.INT.NEG
					  (LIST (DA-TERM.CREATE (DP-FUNCTION.INT.MULT)
								(LIST (DP=INT.INTEGER.CREATE (ABS (CDR FAC.INT))) PRODUCT.TERM)))))))
	   SUM)
     (DA-TERM.CREATE DP*FUNCTION.INT.MAKE_INT (LIST (DA-TERM.CREATE DP*FUNCTION.SIGN.+)
						    (DA-TERM.CREATE DP*FUNCTION.NAT.0))))))


(DEFUN DP=INT.SUM.FACTORIZE (SUM)

  ;;; Input:   a sum
  ;;; Effect:  searches for common factors of all terms of \verb$SUM$
  ;;; Value:   a list of sum denoting the original \verb$SUM$.

  (LET ((FAC.INTS (MAPCAR #'(LAMBDA (X) (CONS (CAR X) (CDR X))) (CAAR SUM))))
    (COND ((EVERY #'(LAMBDA (PROD.INT)
		      (SETQ FAC.INTS (DELETE-IF #'(LAMBDA (FAC.INT1)
						    (EVERY #'(LAMBDA (FAC.INT2)
							       (COND ((UNI-TERM.ARE.EQUAL (CAR FAC.INT1) (CAR FAC.INT2))
								      (SETF (CDR FAC.INT1) (MIN (CDR FAC.INT1) (CDR FAC.INT2)))
								      NIL)
								     (T T)))
							   (CAR PROD.INT)))
						FAC.INTS)))
		  (CDR SUM))
	   (CONS (MAPCAR #'(LAMBDA (PROD.INT)
			     (CONS (REMOVE-IF #'(LAMBDA (FAC.INT1)
						  (SOME #'(LAMBDA (FAC.INT2)
							    (COND ((UNI-TERM.ARE.EQUAL (CAR FAC.INT1) (CAR FAC.INT2))
								   (SETF (CDR FAC.INT1) (- (CDR FAC.INT1) (CDR FAC.INT2)))
								   (ZEROP (CDR FAC.INT1)))))
							 FAC.INTS))
					      (CAR PROD.INT))
				   (CDR PROD.INT)))
			 SUM)
		 (MAPCAR #'(LAMBDA (FAC.INT) (LIST (CONS (LIST (CONS (CAR FAC.INT) 1)) 1)))
			  FAC.INTS)))
	  (T (LIST SUM)))))


(DEFUN DP=INT.SUM.EQUATION.CHECK (SUMS)

  ;;; Input:  a list of sums
  ;;; Effect:
  ;;; Value:  

  (LET (GCD CONST)
    (MAPCAN #'(LAMBDA (SUM)
		   (SETQ GCD 0)
		   (SETQ CONST NIL)
		   (MAPC #'(LAMBDA (PROD.INT)
			     (COND ((NULL (CAR PROD.INT))
				    (SETQ CONST (CDR PROD.INT)))
				   (T (SETQ GCD (GCD GCD (CDR PROD.INT))))))
			 SUM)
		   (COND ((AND CONST (> GCD 0) (NOT (ZEROP (MOD CONST GCD)))) NIL)
			 ((AND CONST (NULL (CDR SUM)) (NEQ CONST 0)) NIL)
			 ((< (ABS GCD) 2) (LIST SUM))
			 (T (LIST (MAPCAR #'(LAMBDA (PROD.INT)
					      (CONS (CAR PROD.INT) (FLOOR (/ (CDR PROD.INT) GCD))))
					  SUM)))))
	       SUMS)))


(DEFUN DP=INT.SUM.TERMS.CREATE (SUM)

  ;;; Input:   a sum (list of dotted pairs: product . integer-value)
  ;;; Effect:  converts sum into two sums:
  ;;;          either there sum is resolved to some constant or is splitted into positive and negative terms of the sum.
  ;;; Value:   multiple-value consisting of both sums

  (LET (ENTRY)
    (COND ((SETQ ENTRY (FIND-IF #'(LAMBDA (FAC.INT)
				 (AND (EQL 1 (LENGTH (CAR FAC.INT)))
				      (EQL 1 (CDR (CAR (CAR FAC.INT))))
				      (EQL 1 (ABS (CDR FAC.INT)))
				      (NULL (DA-TERM.TERMLIST (CAAR (CAR FAC.INT))))
				      (EVERY #'(LAMBDA (FAC.INT2)
						 (OR (EQ FAC.INT FAC.INT2)
						     (EVERY #'(LAMBDA (TERM.INT)
							      (NOT (DA-SYMBOL.OCCURS.IN.GTERM (DA-TERM.SYMBOL (CAAR (CAR FAC.INT)))
											      (CAR TERM.INT))))
							    (CAR FAC.INT2))))
					     SUM)))
			     SUM))
	   (COND ((< (CDR ENTRY) 0)
		  (SETQ SUM (REMOVE ENTRY SUM))
		  (SETQ ENTRY (DP=INT.SUM.ADD.SUM (LIST ENTRY) -1 NIL 0)))
		 (T (SETQ SUM (DP=INT.SUM.ADD.SUM (REMOVE ENTRY SUM)  -1 NIL 0))
		    (SETQ ENTRY (LIST ENTRY)))) 
	   (VALUES (DP=INT.SUM.TERM.CREATE ENTRY) (DP=INT.SUM.TERM.CREATE SUM)))
	  (T (VALUES (DP=INT.SUM.TERM.CREATE (REMOVE-IF #'(LAMBDA (FAC.INT) (< (CDR FAC.INT) 0)) SUM))
		     (DP=INT.SUM.TERM.CREATE (DP=INT.SUM.ADD.SUM (REMOVE-IF #'(LAMBDA (FAC.INT) (> (CDR FAC.INT) 0)) SUM)
							       -1 NIL 0)))))))


;(DEFUN DP=INT.INTEGER.CREATE (INT)

;  ;;; Input:  an integer
;  ;;; Value:  a term which denotes this integer e.g. make_int(+, s(s(0))) for 2.
  
;  (LET (COUNTER ARG)
;    (DA-TERM.CREATE DP*FUNCTION.INT.MAKE_INT (LIST (DA-TERM.CREATE DP*FUNCTION.SIGN.+)
;						   (PROGN (SETQ ARG (DA-TERM.CREATE DP*FUNCTION.NAT.0))
;							  (SETQ COUNTER 0)
;							  (WHILE (< COUNTER INT)
;							    (SETQ ARG (DA-TERM.CREATE DP*FUNCTION.NAT.S (LIST ARG)))
;							    (INCF COUNTER))
;							  ARG)))))
							  
(DEFUN DP=INT.INTEGER.CREATE (INT)

  ;;; 20.08.1996 (Serge)
  ;;; Input:  an integer
  ;;; Value:  a term which denotes this integer e.g. make_int(+, s(s(0))) for 2.
  
  (LET (COUNTER ARG)
    (DA-TERM.CREATE 
     DP*FUNCTION.INT.MAKE_INT 
     (LIST (DA-TERM.CREATE (cond ((< int 0) dp*function.sign.-) (T DP*FUNCTION.SIGN.+)))
	   (PROGN (SETQ ARG (DA-TERM.CREATE DP*FUNCTION.NAT.0))
		  (SETQ COUNTER 0)
		  (WHILE (< COUNTER (abs INT))
		    (SETQ ARG (DA-TERM.CREATE DP*FUNCTION.NAT.S (LIST ARG)))
		    (INCF COUNTER))
		  ARG)))))
							  
  

(DEFUN DP=INT.PRODUCT.TERM.CREATE (PRODUCT)

  ;;; Input:   a product (list of dotted pairs: term . exponent)
  ;;; Effect:  converts product into a term
  ;;; Value:   the corresponding term

  (DA-TERM.FUNCTION.CLOSURE
   (DP-FUNCTION.INT.MULT)
   (MAPCAR #'(LAMBDA (TERM.EXP)
	       (COND ((EQ (CDR TERM.EXP) 1) (CAR TERM.EXP))
		     (T (DA-TERM.FUNCTION.CLOSURE (DP-FUNCTION.INT.MULT)
						  (MAKE-LIST (CDR TERM.EXP) :INITIAL-ELEMENT (CAR TERM.EXP))
						  (DA-TERM.CREATE 1)))))
	   PRODUCT)
   (DA-TERM.CREATE DP*FUNCTION.INT.MAKE_INT (LIST (DA-TERM.CREATE DP*FUNCTION.SIGN.+)
						  (DA-TERM.CREATE DP*FUNCTION.NAT.S (LIST (DA-TERM.CREATE DP*FUNCTION.NAT.0)))))))


(DEFUN DP=INT.SUM.ADD.TERM (SUM INTEGER PRODUCT)

  ;;; Input:   a sum (a list of dotted pairs (product . integer)), an integer, and a product
  ;;; Effect:  inserts the item (integer * product) into sum.
  ;;; Value:   the changed sum

  (LET (ENTRY)
    (COND ((SETQ ENTRY (ASSOC PRODUCT SUM :TEST 'DP=INT.PRODUCT.ARE.EQUAL))
	   (SETF (CDR ENTRY) (+ INTEGER (CDR ENTRY))))
	  (T (PUSH (CONS PRODUCT INTEGER) SUM)))
    SUM))


(DEFUN DP=INT.SUM.NORMALIZE (SUM)

  ;;; Input:  a sum
  ;;; Effect  The terms of \verb$sum$ are sorted according to their size
  ;;; Value:  the sorted sum.

  (SORT SUM #'(LAMBDA (PROD.INT1 PROD.INT2)
		(COND ((NULL (CAR PROD.INT1)) NIL)
		      ((OR (NULL (CAR PROD.INT2))
			   (DA-GTERM.GREATER (CAAAR PROD.INT1) (CAAAR PROD.INT2))
			   (> (CDR (CAR (CAR PROD.INT1))) (CDR (CAR (CAR PROD.INT2))))))))))


(DEFUN DP=INT.SUM.INTEGER (SUM PRODUCT &OPTIONAL INTEGER1)

  ;;; Input:   a sum, a product and an integer
  ;;; Effect:  searches for an item (product . integer) such that integer and integer1
  ;;;          have different signs.
  ;;; Value:   a multiple value:  intege and the item.

  (LET ((ENTRY (ASSOC PRODUCT SUM :TEST 'DP=INT.PRODUCT.ARE.EQUAL)))
    (COND ((AND ENTRY (OR (NULL INTEGER1) (< (* INTEGER1 (CDR ENTRY)) 0)))
	   (VALUES (CDR ENTRY) ENTRY)))))


(DEFUN DP=INT.SUM.ADD.SUM (SUM.1 FACTOR.1 SUM.2 FACTOR.2)

  ;;; Input  : two sums and two integers
  ;;; Effect : multiplies the first sum by the first factor and and also the second sum by
  ;;;          the second factor.
  ;;; Value:   the addition of both multiplied sums

  (LET (PRODUCT.2 RESULT ALL.PRODUCTS.2 INTEGER.2)
    (DP=INT.SUM.NORMALIZE
     (APPEND
      (MAPCAN #'(LAMBDA (PRODUCT.INT)
		  (COND ((MULTIPLE-VALUE-SETQ (INTEGER.2 PRODUCT.2)
			     (DP=INT.SUM.INTEGER SUM.2 (CAR PRODUCT.INT)))
			 (PUSH PRODUCT.2 ALL.PRODUCTS.2)
			 (SETQ RESULT (+ (* (CDR PRODUCT.INT) FACTOR.1) (* INTEGER.2 FACTOR.2)))
			 (COND ((NOT (ZEROP RESULT))
			       (LIST (CONS (CAR PRODUCT.INT) RESULT)))))
			(T (LIST (CONS (CAR PRODUCT.INT) (* (CDR PRODUCT.INT) FACTOR.1))))))
	     SUM.1)
      (MAPCAN #'(LAMBDA (PRODUCT.INT)
		  (COND ((NOT (MEMBER PRODUCT.INT ALL.PRODUCTS.2))
			 (LIST (CONS (CAR PRODUCT.INT) (* (CDR PRODUCT.INT) FACTOR.2))))))
	      SUM.2)))))

 
(DEFUN DP=INT.SUM.MAX.PRODUCTS (SUM)

  ;;; Input:   a sum
  ;;; Effect:  computes all products of sum which are maximal according to the following order:
  ;;;             **missing **
  ;;; Value:   the maximal products of sum.
  
  (LET ((VAR.LIST (MAPCAR #'(LAMBDA (PRODUCT) (DP=INT.PRODUCT.VARIABLES (CAR PRODUCT))) SUM))
	(CONST.LIST (MAPCAR #'(LAMBDA (PRODUCT) (DP=INT.PRODUCT.SKOLEM.CONSTANTS (CAR PRODUCT))) SUM))
	(SIZE.LIST (MAPCAR #'(LAMBDA (PRODUCT) (DP=INT.PRODUCT.SIZE (CAR PRODUCT))) SUM))
	(SYMB.LIST (MAPCAR #'(LAMBDA (PRODUCT)
			       (EVERY #'(LAMBDA (FAC.INT) (DA-VARIABLE.IS (DA-TERM.SYMBOL (CAR FAC.INT)))) (CAR PRODUCT)))
			   SUM))
	RESULT MAX.LIST ALL.VARS)
    (MAPC #'(LAMBDA (VARS) (SETQ ALL.VARS (UNION VARS ALL.VARS))) VAR.LIST)
    (MAPC #'(LAMBDA (PROD.INT.1 VARS1 CONSTS1 SIZE1 SYMB.LIST1)
		       (COND (SYMB.LIST1)
			     ((SET-DIFFERENCE ALL.VARS VARS1))
			     ((EVERY #'(LAMBDA (PROD.INT.2 VARS2 CONSTS2 SIZE2 SYMB.LIST2)
					 (OR (EQ PROD.INT.1 PROD.INT.2)
					     SYMB.LIST2
					     (DP=INT.MSET.DIFFERENCE VARS1 VARS2)
					     (> (+ (LENGTH VARS1) (LENGTH CONSTS1))
						(+ (LENGTH VARS2) (LENGTH CONSTS2)))
					     (AND (EQL (+ (LENGTH VARS1) (LENGTH CONSTS1))
						       (+ (LENGTH VARS2) (LENGTH CONSTS2)))
						  (> SIZE1 SIZE2))
					     (AND (EQL (+ (LENGTH VARS1) (LENGTH CONSTS1))
						       (+ (LENGTH VARS2) (LENGTH CONSTS2)))
						  (EQL SIZE1 SIZE2)
						  (COND ((SOME #'(LAMBDA (FAC.INT.1 FAC.INT.2)
								   (COND ((NOT (DA-GTERM.GREATER (CAR FAC.INT.2) (CAR FAC.INT.1)))
									  (SETQ RESULT 1))
									 ((DA-GTERM.GREATER (CAR FAC.INT.2) (CAR FAC.INT.1))
									  (SETQ RESULT 2))))
							       (CAR PROD.INT.1) (CAR PROD.INT.2))
							 (EQL RESULT 1))))))
				     SUM VAR.LIST CONST.LIST SIZE.LIST SYMB.LIST)
			      (PUSH PROD.INT.1 MAX.LIST))))
	  SUM VAR.LIST CONST.LIST SIZE.LIST SYMB.LIST)
    MAX.LIST))


(DEFUN DP=INT.SUM.DATABASE.ENTRIES (SUM APPLY.FCT)

  ;;; Input:   a sum and a lambda-expression with one parameter
  ;;; Effect:  examines the database and instantiates all usefull inequations and equations
  ;;;          in order to simplify sum.
  ;;; Value:   the list of instantiated (in-)equations.

  (LET ((PRODUCTS (MAPCAN #'(LAMBDA (PROD.INT) (COND ((CAR PROD.INT) (LIST (CAR PROD.INT))))) SUM))
	ACTUAL.PRODUCTS PRODUCT SYMBOL (NEW.SUM.LIST (LIST NIL)) inst.sum dis.sums)
    (SETQ ACTUAL.PRODUCTS PRODUCTS)
    (WHILE ACTUAL.PRODUCTS
      (SETQ PRODUCT (CAR ACTUAL.PRODUCTS))
      (SETQ SYMBOL (DA-TERM.SYMBOL (CAAR PRODUCT)))
      (COND ((DA-FUNCTION.IS SYMBOL)
	     (DB-FUNCTION.DATABASE.COLLECTION
	      (CAAR PRODUCT) 'INEQUALITY
	      #'(LAMBDA (FACI.PODI.SUM.CONDITION)
		  (MAPC #'(LAMBDA (SUBST)
			    (COND ((OR (NULL (FOURTH FACI.PODI.SUM.CONDITION))
				       (FUNCALL APPLY.FCT (MAPCAR #'(LAMBDA (LIT)
								      (CAAAR (DP=INT.SUBST.INST.FAC (CONS LIT 1) SUBST)))
								  (FOURTH FACI.PODI.SUM.CONDITION))))
				   (SETQ inst.sum (DP=INT.SUBST.INSTANTIATE (THIRD FACI.PODI.SUM.CONDITION) SUBST))
				   (MAPL #'(LAMBDA (NEW.SUMS.TAIL) (PUSH INST.SUM (CAR NEW.SUMS.TAIL))) NEW.SUM.LIST)
				   (SETQ PRODUCTS (DP=INT.ADD.PRODUCTS PRODUCTS inst.sum)))))		     
			(DP=INT.PRODUCT.MATCH.AC1 (CAR (SECOND FACI.PODI.SUM.CONDITION))
						  PRODUCT
						  NIL))
		  NIL))
	     (DB-FUNCTION.DATABASE.COLLECTION
	      (CAAR PRODUCT) 'EQUALITY
	      #'(LAMBDA (FACI.PODI.SUM.CONDITION)
		  (MAPC #'(LAMBDA (SUBST)
			    (COND ((OR (NULL (FOURTH FACI.PODI.SUM.CONDITION))
				       (FUNCALL APPLY.FCT (MAPCAR #'(LAMBDA (LIT)
								      (CAAAR (DP=INT.SUBST.INST.FAC (CONS LIT 1) SUBST)))
								  (FOURTH FACI.PODI.SUM.CONDITION))))
				   (setq inst.sum (DP=INT.SUBST.INSTANTIATE (THIRD FACI.PODI.SUM.CONDITION) SUBST))
				   (MAPL #'(LAMBDA (NEW.SUMS.TAIL)
					     (PUSH INST.SUM (CAR NEW.SUMS.TAIL))
					     (push (dp=int.sum.add.sum inst.sum -1 nil 1) (CAR NEW.SUMS.TAIL)))
					 NEW.SUM.LIST)
					(SETQ PRODUCTS (DP=INT.ADD.PRODUCTS PRODUCTS inst.sum)))))
			(DP=INT.PRODUCT.MATCH.AC1 (CAR (SECOND FACI.PODI.SUM.CONDITION))
						  PRODUCT NIL))
		  NIL))
	     (DB-FUNCTION.DATABASE.COLLECTION
	      (CAAR PRODUCT) 'DISJUNCTION
	      #'(LAMBDA (FACI.PODI.SUM.CONDITION)
		  (MAPC #'(LAMBDA (SUBST)
			    (COND ((OR (NULL (FOURTH FACI.PODI.SUM.CONDITION))
				       (FUNCALL APPLY.FCT (MAPCAR #'(LAMBDA (LIT)
								      (CAAAR (DP=INT.SUBST.INST.FAC (CONS LIT 1) SUBST)))
								  (FOURTH FACI.PODI.SUM.CONDITION))))
				   (SETQ DIS.SUMS NIL)
				   (MAPC #'(LAMBDA (NEW.SUM)
					     (setq inst.sum (DP=INT.SUBST.INSTANTIATE NEW.SUM SUBST))
					     (MAPC #'(LAMBDA (SUM.LIST)
						       (PUSH (CONS inst.sum SUM.LIST) DIS.SUMS))
						   NEW.SUM.LIST))
					 (THIRD FACI.PODI.SUM.CONDITION))
				   (SETQ NEW.SUM.LIST DIS.SUMS)
				   (SETQ PRODUCTS (DP=INT.ADD.PRODUCTS PRODUCTS inst.sum)))))
			(DP=INT.PRODUCT.MATCH.AC1 (CAR (SECOND FACI.PODI.SUM.CONDITION))
						  PRODUCT NIL))
		  NIL))))
      (POP ACTUAL.PRODUCTS))
    NEW.SUM.LIST))


(DEFUN DP=INT.ADD.PRODUCTS (PRODS SUM)

  (LET ((NEW.PRODS (MAPCAN #'(LAMBDA (PROD.INT)
			       (COND ((AND (CAR PROD.INT)
					   (NOT (MEMBER (CAR PROD.INT) PRODS :TEST #'DP=INT.PRODUCT.ARE.EQUAL)))
				      (LIST (CAR PROD.INT)))))
			   SUM)))
    (NCONC PRODS NEW.PRODS)))


(DEFUN DP=INT.SUBST.INSTANTIATE (SUM SUBST)

  ;;; Input:   a sum and a integer-substitution
  ;;; Effect:  instantiate sum by the given substitution
  ;;; Value:   the instantiated (and normalized) sum
  
  (DP=INT.SUM.NORMALIZE (MAPCAR #'(LAMBDA (PROD.INT)
				    (DP=INT.SUBST.INST.PROD PROD.INT SUBST))
				SUM)))


(DEFUN DP=INT.SUBST.INST.PROD (PROD.INT SUBST)

  ;;; Input:   a product and an integer-subst
  ;;; Effect:  instantiate product by the given substitution
  ;;; Value:   the instantiated (and normalized) product

  (LET (NEW.PROD NEW.PROD.INT (NEW.INT (CDR PROD.INT)))
    (SETQ NEW.PROD (DP=INT.PRODUCT.NORMALIZE (MAPCAN #'(LAMBDA (FAC.INT)
							 (SETQ NEW.PROD.INT (DP=INT.SUBST.INST.FAC FAC.INT SUBST))
							 (SETQ NEW.INT (* (CDR NEW.PROD.INT) NEW.INT))
							 (CAR NEW.PROD.INT))
						     (CAR PROD.INT))))
    (CONS NEW.PROD NEW.INT)))


(DEFUN DP=INT.SUBST.INST.FAC (FAC.INT SUBST)

  ;;; Input:   a factor and an integer-subst
  ;;; Effect:  instantiate term by the given substitution
  ;;; Value:   a product.integer which denotes the instantiated (and normalized) factor

  (LET (ENTRY TAFS TERM)
    (COND ((DA-VARIABLE.IS (DA-GTERM.SYMBOL (CAR FAC.INT)))
	   (COND ((SETQ ENTRY (ASSOC (DA-GTERM.SYMBOL (CAR FAC.INT)) SUBST))
		  (CONS (MAPCAR #'(LAMBDA (FAC.INT2) (CONS (CAR FAC.INT2) (* (CDR FAC.INT2) (CDR FAC.INT))))
				(CAR (CDR ENTRY)))
			(EXPT (CDR (CDR ENTRY)) (CDR FAC.INT))))
		 (T (CONS (LIST FAC.INT) 1))))
	  ((SETQ TAFS (DA-GTERM.TAFS (CAR FAC.INT)
				     #'(LAMBDA (SUBTERM)
					 (AND (DA-VARIABLE.IS (DA-GTERM.SYMBOL SUBTERM))
					      (ASSOC (DA-GTERM.SYMBOL SUBTERM) SUBST)))))
	   (SETQ TERM (DA-GTERM.COPY (CAR FAC.INT)))
	   (MAPC #'(LAMBDA (TAF)
		     (DA-REPLACE TAF TERM
				 (DP=INT.PRODUCT.TERM.CREATE
				  (CAR (CDR (ASSOC (DA-GTERM.SYMBOL (DA-ACCESS TAF TERM)) SUBST))))))
		 TAFS)
	   (CONS (LIST (CONS TERM (CDR FAC.INT))) 1))
	  (T (CONS (LIST FAC.INT) 1)))))


  
;;; products:


(defun DP=INT.PRODUCT.NORMALIZE (PRODUCT)
  
  ;;; Input:   a list of terms denoting a product
  ;;; Effect:  sorts the factors according the gterm-size and groups the equal elements
  ;;; Value:   a list of dotted pairs (term . exponent) which is called a product
  
  (LET (RESULT (COUNTER 0) OLD.TERM)
    (MAPC #'(LAMBDA (FAC.INT) (SETF (CAR FAC.INT) (DP=INT.FACTOR.NORMALIZE (CAR FAC.INT)))) PRODUCT)
    (SETQ RESULT (MAPCAN #'(LAMBDA (FAC.INT)
			     (COND ((AND OLD.TERM (UNI-TERM.ARE.EQUAL OLD.TERM (CAR FAC.INT)))
				    (INCF COUNTER (CDR FAC.INT))
				    NIL)
				   (T (PROG1 (COND (OLD.TERM (LIST (CONS OLD.TERM COUNTER))))
					(SETQ OLD.TERM (CAR FAC.INT))
					(SETQ COUNTER (CDR FAC.INT))))))
			 (SORT PRODUCT #'(LAMBDA (X Y) (DA-GTERM.GREATER (CAR X) (CAR Y))))))
    (COND (OLD.TERM (SETQ RESULT (NCONC RESULT (LIST (CONS OLD.TERM COUNTER))))))
    RESULT))


(DEFUN DP=INT.FACTOR.NORMALIZE (FACTOR)

  (COND ((NUMBERP (DA-TERM.SYMBOL FACTOR))
	 (dp=int.integer.create (DA-TERM.SYMBOL FACTOR)))
	(T (MAPL #'(LAMBDA (TERMLIST)
		     (SETF (CAR TERMLIST) (DP=INT.FACTOR.NORMALIZE (CAR TERMLIST))))
		 (DA-GTERM.TERMLIST FACTOR))
	   FACTOR)))


(DEFUN DP=INT.PRODUCT.VARIABLES (PRODUCT)

  ;;; Input:  a product (e.g a list of dotted pairs (gterm . exponent)
  ;;; Value:  the list of all variables occurring in \verb$PRODUCT$
  
  (LET (VARS)
    (MAPC #'(LAMBDA (GTERM.EXP)
	      (SETQ VARS (NCONC (DA-GTERM.VARIABLES (CAR GTERM.EXP)) VARS)))
	  PRODUCT)
    VARS))


(DEFUN DP=INT.PRODUCT.SKOLEM.CONSTANTS (PRODUCT)

  ;;; Input:  a product (e.g a list of dotted pairs (gterm . exponent)
  ;;; Value:  the list of all skolem constants occurring in \verb$PRODUCT$
  
  (LET (VARS)
    (MAPC #'(LAMBDA (GTERM.EXP)
	      (SETQ VARS (NCONC (DA-GTERM.CONSTANTS (CAR GTERM.EXP) 'SKOLEM) VARS)))
	  PRODUCT)
    VARS))


(DEFUN DP=INT.PRODUCT.ARE.EQUAL (X Y)

  ;;; Input:  two products
  ;;; Value:  T, iff both products are equal.
  
  (AND (EQL (LENGTH X) (LENGTH Y))
       (EVERY #'(LAMBDA (X1 Y1) (AND (EQL (CDR X1) (CDR Y1))
				     (UNI-TERM.ARE.EQUAL (CAR X1) (CAR Y1))))
	      X Y)))


(DEFUN DP=INT.PRODUCT.SIZE (PRODUCT)
  
  ;;; Input:  a product
  ;;; Value:  the term size of the denoted gterm
  
  (LET ((SIZE 0))
    (MAPC #'(LAMBDA (TERM.EXP) (INCF SIZE (* (CDR TERM.EXP) (DA-GTERM.SIZE (CAR TERM.EXP)))))
	  PRODUCT)
    SIZE))


(DEFUN DP=INT.PRODUCT.MATCH.AC1 (PRODUCT1 PRODUCT2 SUBST)
  
  ;;; Input:  two products and an assoc-list (denoting a substitution)
  ;;; Effect: tries to match \verb$PRODUCT1$ against \verb$PRODUCT2$ regarding
  ;;;         \verb$SUBST$. This is done under the theory of associativity and
  ;;;         commutativity
  ;;; Value:  a list of assoc-lists denoting the possible matcher of both products
  
  (LET ((FAC.INT.1 (CAR PRODUCT1)) RESULT ENTRY NEW.PRODUCT1 NEW.PRODUCT2 NEW.SUBST OLD.SUBST)
    (COND ((NULL PRODUCT1)
	   (COND ((NULL PRODUCT2) (LIST SUBST))))
	  ((AND PRODUCT1 (NULL PRODUCT2)) ; SUPERFLUOUS VARIABLES MATCHING EMPTY LIST
	   (COND ((EVERY #'(LAMBDA (FAC.INT.1)
			     (AND (DA-VARIABLE.IS (DA-TERM.SYMBOL (CAR FAC.INT.1)))
				  (NULL (ASSOC (DA-TERM.SYMBOL (CAR FAC.INT.1)) SUBST))))
			 PRODUCT1)
		  (LIST (CONS (NCONC (MAPCAR #'(LAMBDA (VAR) (CONS VAR NIL)) PRODUCT1) SUBST)
			      NIL)))))
	  ((AND (DA-VARIABLE.IS (DA-TERM.SYMBOL (CAR FAC.INT.1))) ; VARIABLE WITH BINDING
		(SETQ ENTRY (ASSOC (DA-TERM.SYMBOL (CAR FAC.INT.1)) SUBST)))
	   (COND ((EVERY #'(LAMBDA (FAC.INT.2)
			     (COND ((MEMBER FAC.INT.2 PRODUCT2 :TEST
					    #'(LAMBDA (X Y) (AND (EQL (CDR X) (CDR Y)) (UNI-TERM.ARE.EQUAL (CAR X) (CAR Y)))))
				    (SETQ PRODUCT2 (REMOVE FAC.INT.2 PRODUCT2 :TEST
							   #'(LAMBDA (X Y) (AND (EQL (CDR X) (CDR Y))
										(UNI-TERM.ARE.EQUAL (CAR X) (CAR Y))))
							   :COUNT 1))
				    T)))
			 (CDR ENTRY))
		  (DP=INT.PRODUCT.MATCH.AC1 (CDR PRODUCT1) PRODUCT2 SUBST))))
	  ((DA-VARIABLE.IS (DA-TERM.SYMBOL (CAR FAC.INT.1)))
	   (MAPCAN #'(LAMBDA (PERMUTATION)
		       (SETQ NEW.PRODUCT2 (COPY-LIST PRODUCT2))
		       (MAPC #'(LAMBDA (FAC.INT.2)
				 (SETF (CDR FAC.INT.2) (CDR FAC.INT.1))
				 (SETQ NEW.PRODUCT2 (DP=INT.PRODUCT.REMOVE.FAC.INT PRODUCT2 FAC.INT.2)))
			     PERMUTATION)
		       (SETQ NEW.SUBST (ACONS (DA-TERM.SYMBOL (CAR FAC.INT.1)) PERMUTATION SUBST))
		       (DP=INT.PRODUCT.MATCH.AC1 NEW.PRODUCT1 NEW.PRODUCT2 NEW.SUBST))
		   (POWERSET (REMOVE-IF #'(LAMBDA (FAC.INT) (< (CDR FAC.INT) (CDR FAC.INT.1))) PRODUCT2)
			     :TEST #'DP=INT.PRODUCT.ARE.EQUAL)))
	  (T (MAPCAN #'(LAMBDA (FAC.INT.2)
			 (MAPCAN #'(LAMBDA (NEW.SUBST)
				     (SETQ OLD.SUBST SUBST)
				     (COND ((EVERY #'(LAMBDA (VAR)
						       (SETQ RESULT (DP=INT.TERM.FACTORIZE
								      (UNI-SUBST.APPLY NEW.SUBST (DA-TERM.CREATE VAR))))
						       (COND ((SETQ ENTRY (ASSOC VAR OLD.SUBST))
							      (DP=INT.PRODUCT.ARE.EQUAL RESULT (CDR ENTRY)))
							     (T (PUSH (CONS VAR RESULT) OLD.SUBST))))
						   (UNI-SUBST.DOMAIN NEW.SUBST))
					    (DP=INT.PRODUCT.MATCH.AC1 (CDR PRODUCT1)
								      (DP=INT.PRODUCT.REMOVE.FAC.INT
								       PRODUCT2 (CONS (CAR FAC.INT.2) (CDR FAC.INT.1)))
								      OLD.SUBST))))
				 (COND ((<= (CDR FAC.INT.1) (CDR FAC.INT.2))
					(UNI-TERM.MATCH (CAR FAC.INT.1) (CAR FAC.INT.2) T)))))
		     PRODUCT2)))))


(DEFUN DP=INT.PRODUCT.REMOVE.FAC.INT (PRODUCT FAC.INT)

  ;;; Input:  a product and an factor
  ;;; Effect: subtracts \verb$FAC.INT$ from \verb$PRODUCT$
  ;;; Value:  the result of subtraction
  
  (LET (ENTRY)
    (SETQ PRODUCT (COPY-TREE PRODUCT))
    (COND ((SETQ ENTRY (ASSOC (CAR FAC.INT) PRODUCT))
	   (SETF (CDR ENTRY) (- (CDR ENTRY) (CDR FAC.INT)))
	   (COND ((ZEROP (CDR ENTRY)) (DELETE ENTRY PRODUCT))
		 (T PRODUCT))))))


(DEFUN DP=INT.MSET.DIFFERENCE (S2 S1)

  (SETQ S2 (COPY-LIST S2))
  (MAPC #'(LAMBDA (VAR)
	    (SETQ S2 (DELETE VAR S2 :COUNT 1)))
	S1)
  S2)


;;;;;================================================================================================
;;;;;
;;;;; Definition of datatype SET:
;;;;;
;;;;;================================================================================================

(DEFVAR DP*SET.NAMES (LIST "empty" "insert" "element" "subset" "elem" "delete" "+" "*" "\\" "-" "<=" ">="))

(DEFVAR DP*SET.CONSTRUCTOR.NAMES (LIST "empty" "insert"))


(DEFMACRO DP-SET.NAMES ()
  ;;; Edited : 21.04.94 by CS
  ;;; Input  : none
  ;;; Value  : a list of strings denoting the predefined functions and predicates over sets
  
  'DP*SET.NAMES)


(DEFMACRO DP-SET.CONSTRUCTOR.NAMES ()
  
  ;;; Edited : 21.04.94 by CS
  ;;; Input  : none
  ;;; Value  : a list of strings denoting the predefined constructor functions over sets
  
  'DP*SET.CONSTRUCTOR.NAMES)


(DEFUN DP-INSTANTIATE.SET.SPEC
  (SET.SORT ELEMENT.SORT SET.EMPTY SET.INSERT SET.ELEMENT SET.SUBSET SET.ELEM)

  ;;; Edited : 21.04.94 by CS
  ;;; Input  : the names for the new set data type, its element sort, its constructors empty and insert,
  ;;;          its destructors element and subset, and the $\in$ relation
  ;;; Value  : generates a string for the insertion of the following set specification (instantiated with
  ;;;          the above parameters):
  ;;;          .
  ;;;          .non-free structure
  ;;;          .   empty,
  ;;;          .   insert(element:element_type, subset:set):set
  ;;;          . {d-predicate elem(element_type, set)
  ;;;          .    {axiom all x:element_type not elem(x, empty)
  ;;;          .     axiom all A:set all x,y:element_type
  ;;;          .             elem(x, insert(y, A)) eqv
  ;;;          .                (x = y or elem(x, A))}
  ;;;          .  axiom all A,B:set
  ;;;          .          (all x:element_type elem(x, A) eqv
  ;;;          .             elem(x, B))
  ;;;          .          impl A = B }
	   
  (list (LIST (LIST (FORMAT NIL "non-free structure ~A, ~A(~A:~A, ~A:~A):~A {"
		       SET.EMPTY SET.INSERT SET.ELEMENT ELEMENT.SORT SET.SUBSET SET.SORT SET.SORT)
	       (FORMAT NIL "   d-predicate ~A(~A, ~A) {"
		       SET.ELEM ELEMENT.SORT SET.SORT)
	       (FORMAT NIL "      axiom all x:~A not ~A(x, ~A)"
		       ELEMENT.SORT SET.ELEM SET.EMPTY)
	       (FORMAT NIL "      axiom all A:~A all x,y:~A ~A(x, ~A(y, A)) eqv (x = y or ~A(x, A))"
		       SET.SORT ELEMENT.SORT SET.ELEM SET.INSERT SET.ELEM)
	       (FORMAT NIL "   }")
	       (FORMAT NIL "   axiom all A,B:~A (all x:~A ~A(x, A) eqv ~A(x, B)) impl A = B"
		       SET.SORT ELEMENT.SORT SET.ELEM SET.ELEM)
	       (FORMAT NIL "}")) NIL)))


(DEFUN DP-INSTANTIATE.SET.INPUT
  (SET.SORT ELEMENT.SORT SET.EMPTY SET.INSERT SET.ELEMENT SET.SUBSET SET.DELTA.SUBSET SET.ELEM SET.DELETE 
	    SET.DELTA.DELETE SET.UNION SET.INTERSECTION SET.DIFFERENCE SET.SYM.DIFFERENCE SET.<= 
	    SET.>= SET.DELTA.INTERSECTION.1 SET.DELTA.INTERSECTION.2 SET.DELTA.DIFFERENCE)
  
  ;;; Edited : 21.04.94 by CS
  ;;; Input  : the names for the new set data type, its element sort, its constructors empty and insert,
  ;;;          its destructors element and subset, its delta difference predicate for subset, its $\in$ relation,
  ;;;          its delete function, its delta difference predicate for delete, its union function, its
  ;;;          intersection function, its difference function, its symetric difference function,
  ;;;          its $\subseteq$ relation, its $\supseteq$ relation, and its difference predicates for
  ;;;          intersection and difference
  ;;; Value  : generates a string for the insertion of the following specification of the predefined
  ;;;          set functions and predicates (instantiated with the above parameters) together with some
  ;;;          simplification lemmata:
  ;;;          .
  ;;;          .axiom all A,B:set all x:element_type
  ;;;          .   A = insert(x, B) impl
  ;;;          .      A = insert(element(A), subset(A))
  ;;;          .
  ;;; 	       .axiom subset(empty) = empty
  ;;;          .
  ;;; 	       .axiom all A:set A = insert(element(A), subset(A))
  ;;;          .         impl not A = subset(A)
  ;;;          .
  ;;;          .a-predicate delta-subset(A:set) = 
  ;;; 	       .   A = insert(element(A), subset(A))
  ;;; 	       .
  ;;; 	       .a-function delete(x:element_type, A:set):set =
  ;;; 	       .   if A of empty then empty
  ;;; 	       .   if A of insert and x = element(A) then
  ;;;          .      subset(A)
  ;;; 	       .   otherwise
  ;;;          .      insert(element(A), delete(x, subset(A)))
  ;;; 	       .
  ;;; 	       .a-predicate delta-delete-2(x:element_type, A:set) =  
  ;;; 	       .   elem(x, A)
  ;;; 	       .
  ;;; 	       .a-function +(A,B:set):set =
  ;;; 	       .   if A of empty then B
  ;;;          .   otherwise insert(element(A), +(subset(A), B))
  ;;; 	       .
  ;;; 	       .a-function *(A,B:set):set =
  ;;; 	       .   if A of empty then empty
  ;;; 	       .   if A of insert and elem(element(A), B) then
  ;;;          .      insert(element(A), *(subset(A), B))
  ;;; 	       .   otherwise *(subset(A), B)
  ;;; 	       .
  ;;; 	       .a-function \(A,B:set):set =
  ;;; 	       .   if A of empty then empty
  ;;; 	       .   if A of insert and elem(element(A), B) then
  ;;;          .      \(subset(A), B)
  ;;; 	       .   otherwise insert(element(A), \(subset(A), B))
  ;;; 	       .
  ;;; 	       .a-function -(A,B:set):set =
  ;;; 	       .   ((A \ B) + (B \ A))
  ;;; 	       .
  ;;; 	       .d-predicate <=(set, set) {
  ;;; 	       .   axiom all A,B:set all x:element_type 
  ;;; 	       .      <=(A, B) eqv (elem(x, A) impl elem(x, B))
  ;;; 	       .}
  ;;; 	       .
  ;;; 	       .d-predicate >=(set, set) {
  ;;; 	       .   axiom all A,B:set all x:element_type 
  ;;; 	       .      >=(A, B) eqv (elem(x, B) impl elem(x, A))
  ;;; 	       .}
  ;;;          .
  ;;; 	       .a-predicate delta-*-1(A,B:set) =
  ;;; 	       .   if A of empty then false
  ;;; 	       .   if A of insert and not elem(element(A), B) then
  ;;;          .      true
  ;;; 	       .   otherwise delta-*-1(subset(A), B)
  ;;;          .
  ;;; 	       .a-predicate delta-*-2(A,B:set) =
  ;;; 	       .   if B of empty then false
  ;;; 	       .   if B of insert and not elem(element(B), A) then
  ;;;          .      true
  ;;; 	       .   otherwise delta-*-2(A, subset(B))
  ;;; 	       .
  ;;; 	       .a-predicate delta-\-1(A,B:set) =
  ;;; 	       .   if A of empty then false
  ;;; 	       .   if A of insert and elem(element(A), B) then
  ;;;          .      true
  ;;; 	       .   otherwise delta-\-1(subset(A), B)
  ;;; 	       .
  ;;;          .axiom all A:set
  ;;;          .   element(insert(element(A), subset(A))) =
  ;;;          .      element(A)
  ;;;          .
  ;;;          .axiom all A:set
  ;;;          .   subset(insert(element(A), subset(A))) =
  ;;;          .      subset(A)
	  
  (LIST (LIST (LIST (FORMAT NIL "axiom all A,B:~A all x:~A"
		       SET.SORT ELEMENT.SORT)
	       (FORMAT NIL "  A = ~A(x, B) impl A = ~A(~A(A), ~A(A))"
		       SET.INSERT SET.INSERT SET.ELEMENT SET.SUBSET))
	      (LIST (LIST (FORMAT NIL "all A,B:~A all x:~A"
			SET.SORT ELEMENT.SORT)
		(FORMAT NIL "  A = ~A(x, B) impl A = ~A(~A(A), ~A(A))"
			SET.INSERT SET.INSERT SET.ELEMENT SET.SUBSET))))
	
	(LIST (LIST (FORMAT NIL "axiom ~A(~A) = ~A"
		       SET.SUBSET SET.EMPTY SET.EMPTY))
	      (LIST (LIST (FORMAT NIL "~A(~A) = ~A"
			SET.SUBSET SET.EMPTY SET.EMPTY))))
	
	(LIST (LIST (FORMAT NIL "axiom all A:~A A = ~A(~A(A), ~A(A)) impl not A = ~A(A)"
		       SET.SORT SET.INSERT SET.ELEMENT SET.SUBSET SET.SUBSET))
	      (LIST (LIST (FORMAT NIL "all A:~A A = ~A(~A(A), ~A(A)) impl not A = ~A(A)"
			SET.SORT SET.INSERT SET.ELEMENT SET.SUBSET SET.SUBSET))))

	(LIST (LIST (FORMAT NIL "a-predicate ~A(A:~A) = "
		       SET.DELTA.SUBSET SET.SORT)
	       (FORMAT NIL "   A = ~A(~A(A), ~A(A))"
		       SET.INSERT SET.ELEMENT SET.SUBSET)) nil)
	
	(LIST (LIST (FORMAT NIL "a-function ~A(x:~A, A:~A):~A ="
		       SET.DELETE ELEMENT.SORT SET.SORT SET.SORT)
		    (FORMAT NIL "   if A of ~A then ~A"
			    SET.EMPTY SET.EMPTY)
		    (FORMAT NIL "   if A of ~A and x = ~A(A) then ~A(A)"
			    SET.INSERT SET.ELEMENT SET.SUBSET)
		    (FORMAT NIL "   otherwise ~A(~A(A), ~A(x, ~A(A)))"
			    SET.INSERT SET.ELEMENT SET.DELETE SET.SUBSET))
	      (LIST (LIST (FORMAT NIL "all x:~A all A:~A (not A = ~A or (not A = ~A(~A(A), ~A(A)) or not x = ~A(A)))"
			ELEMENT.SORT SET.SORT SET.EMPTY SET.INSERT SET.ELEMENT SET.SUBSET SET.ELEMENT))))
	
	(LIST (LIST (FORMAT NIL "a-predicate ~A(x:~A, A:~A) =  "
		       SET.DELTA.DELETE ELEMENT.SORT SET.SORT)
	       (FORMAT NIL "   ~A(x, A)"
		       SET.ELEM)) nil)
	
	(LIST (LIST (FORMAT NIL "a-function ~A(A,B:~A):~A ="
		       SET.UNION SET.SORT SET.SORT)
	       (FORMAT NIL "   if A of ~A then B"
		       SET.EMPTY)
	       (FORMAT NIL "   otherwise ~A(~A(A), ~A(~A(A), B))"
		       SET.INSERT SET.ELEMENT SET.UNION SET.SUBSET)) nil)
	
	(LIST (LIST (FORMAT NIL "a-function ~A(A,B:~A):~A ="
		       SET.INTERSECTION SET.SORT SET.SORT)
	       (FORMAT NIL "   if A of ~A then ~A"
		       SET.EMPTY SET.EMPTY)
	       (FORMAT NIL "   if A of ~A and ~A(~A(A), B) then ~A(~A(A), ~A(~A(A), B))"
		       SET.INSERT SET.ELEM SET.ELEMENT SET.INSERT SET.ELEMENT SET.INTERSECTION SET.SUBSET)
	       (FORMAT NIL "   otherwise ~A(~A(A), B)"
		       SET.INTERSECTION SET.SUBSET))
	      (LIST (LIST (FORMAT NIL "all B:~A all A:~A"
			SET.SORT SET.SORT)
		(FORMAT NIL "   (not A = ~A or (not A = ~A(~A(A), ~A(A)) or not ~A(~A(A), B)))"
			SET.EMPTY SET.INSERT SET.ELEMENT SET.SUBSET SET.ELEM SET.ELEMENT))))
	
	(LIST (LIST (FORMAT NIL "a-function ~A(A,B:~A):~A ="
		       SET.DIFFERENCE SET.SORT SET.SORT)
	       (FORMAT NIL "   if A of ~A then ~A"
		       SET.EMPTY SET.EMPTY)
	       (FORMAT NIL "   if A of ~A and ~A(~A(A), B) then ~A(~A(A), B)"
		       SET.INSERT SET.ELEM SET.ELEMENT SET.DIFFERENCE SET.SUBSET)
	       (FORMAT NIL "   otherwise ~A(~A(A), ~A(~A(A), B))"
		       SET.INSERT SET.ELEMENT SET.DIFFERENCE SET.SUBSET))
	      (LIST (LIST (FORMAT NIL "all B:~A all A:~A"
			SET.SORT SET.SORT)
		(FORMAT NIL "   (not A = ~A or (not A = ~A(~A(A), ~A(A)) or not ~A(~A(A), B)))"
			SET.EMPTY SET.INSERT SET.ELEMENT SET.SUBSET SET.ELEM SET.ELEMENT))))
	
	(LIST (LIST (FORMAT NIL "a-function ~A(A,B:~A):~A ="
		       SET.SYM.DIFFERENCE SET.SORT SET.SORT)
	       (FORMAT NIL "   ((A ~A B) ~A (B ~A A))"
		       SET.DIFFERENCE SET.UNION SET.DIFFERENCE)) nil)
	
	(LIST (LIST (FORMAT NIL "d-predicate ~A(~A, ~A) {"
		       SET.<= SET.SORT SET.SORT)
	       (FORMAT NIL "   axiom all A,B:~A all x:~A "
		       SET.SORT ELEMENT.SORT)
	       (FORMAT NIL "      ~A(A, B) eqv (~A(x, A) impl ~A(x, B))"
		       SET.<= SET.ELEM SET.ELEM)
	       (FORMAT NIL "}")) nil)
	
	(LIST (LIST (FORMAT NIL "d-predicate ~A(~A, ~A) {"
		       SET.>= SET.SORT SET.SORT)
	       (FORMAT NIL "   axiom all A,B:~A all x:~A "
		       SET.SORT ELEMENT.SORT)
	       (FORMAT NIL "      ~A(A, B) eqv (~A(x, B) impl ~A(x, A))"
		       SET.>= SET.ELEM SET.ELEM)
	       (FORMAT NIL "}")) nil)
	(LIST (LIST (FORMAT NIL "a-predicate ~A(A,B:~A) ="
		       SET.DELTA.INTERSECTION.1 SET.SORT)
	       (FORMAT NIL "   if A of ~A then false"
		       SET.EMPTY)
	       (FORMAT NIL "   if A of ~A and not ~A(~A(A), B) then true"
		       SET.INSERT SET.ELEM SET.ELEMENT)
	       (FORMAT NIL "   otherwise ~A(~A(A), B)"
		       SET.DELTA.INTERSECTION.1 SET.SUBSET))
	      (LIST (LIST (FORMAT NIL "all B:~A all A:~A "
			SET.SORT SET.SORT)
		(FORMAT NIL "   (not A = ~A or (not A = ~A(~A(A), ~A(A)) or not ~A(~A(A), B)))"
			SET.EMPTY SET.INSERT SET.ELEMENT SET.SUBSET SET.ELEM SET.ELEMENT))))
	(LIST (LIST (FORMAT NIL "a-predicate ~A(A,B:~A) ="
		       SET.DELTA.INTERSECTION.2 SET.SORT)
	       (FORMAT NIL "   if B of ~A then false"
		       SET.EMPTY)
	       (FORMAT NIL "   if B of ~A and not ~A(~A(B), A) then true"
		       SET.INSERT SET.ELEM SET.ELEMENT)
	       (FORMAT NIL "   otherwise ~A(A, ~A(B))"
		       SET.DELTA.INTERSECTION.2 SET.SUBSET))
	      (LIST (LIST (FORMAT NIL "all B:~A all A:~A "
			SET.SORT SET.SORT)
		(FORMAT NIL "   (not A = ~A or (not A = ~A(~A(A), ~A(A)) or not ~A(~A(A), B)))"
			SET.EMPTY SET.INSERT SET.ELEMENT SET.SUBSET SET.ELEM SET.ELEMENT))))
	(LIST (LIST (FORMAT NIL "a-predicate ~A(A,B:~A) ="
		       SET.DELTA.DIFFERENCE SET.SORT)
	       (FORMAT NIL "   if A of ~A then false"
		       SET.EMPTY)
	       (FORMAT NIL "   if A of ~A and ~A(~A(A), B) then true"
		       SET.INSERT SET.ELEM SET.ELEMENT)
	       (FORMAT NIL "   otherwise ~A(~A(A), B)"
		       SET.DELTA.DIFFERENCE SET.SUBSET))
	      (LIST (LIST (FORMAT NIL "all B:~A all A:~A "
			SET.SORT SET.SORT)
		(FORMAT NIL "   (not A = ~A or (not A = ~A(~A(A), ~A(A)) or not ~A(~A(A), B)))"
			SET.EMPTY SET.INSERT SET.ELEMENT SET.SUBSET SET.ELEM SET.ELEMENT))))

	(LIST (LIST (FORMAT NIL "axiom all A:~A"
			    SET.SORT)
		    (FORMAT NIL "   ~A(~A(~A(A), ~A(A))) = ~A(A)"
			    SET.ELEMENT SET.INSERT SET.ELEMENT SET.SUBSET SET.ELEMENT))
	      (LIST (LIST (FORMAT NIL "all A:~A"
			    SET.SORT)
			  (FORMAT NIL "   ~A(~A(~A(A), ~A(A))) = ~A(A)"
				  SET.ELEMENT SET.INSERT SET.ELEMENT SET.SUBSET SET.ELEMENT))))
	
	(LIST (LIST (FORMAT NIL "axiom all A:~A"
			    SET.SORT)
		    (FORMAT NIL "   ~A(~A(~A(A), ~A(A))) = ~A(A)"
			    SET.SUBSET SET.INSERT SET.ELEMENT SET.SUBSET SET.SUBSET))
	      (LIST (LIST (FORMAT NIL "all A:~A"
			    SET.SORT)
			  (FORMAT NIL "   ~A(~A(~A(A), ~A(A))) = ~A(A)"
				  SET.SUBSET SET.INSERT SET.ELEMENT SET.SUBSET SET.SUBSET))))
	))


;;;;;================================================================================================
;;;;;
;;;;; ;;; Variables for the datatype SET
;;;;;
;;;;;================================================================================================

(DEFVAR DP*SORT.SET NIL)
(DEFVAR DP*SORT.ELEMENT.TYPE NIL)

(DEFVAR DP*FUNCTION.SET.EMPTY NIL)
(DEFVAR DP*FUNCTION.SET.INSERT NIL)
(DEFVAR DP*FUNCTION.SET.ELEMENT NIL)
(DEFVAR DP*FUNCTION.SET.SUBSET NIL)
(DEFVAR DP*FUNCTION.SET.DELETE NIL)
(DEFVAR DP*FUNCTION.SET.INTERSECTION NIL)
(DEFVAR DP*FUNCTION.SET.DIFFERENCE NIL)
(DEFVAR DP*FUNCTION.SET.UNION NIL)
(DEFVAR DP*FUNCTION.SET.SYM.DIFFERENCE NIL)

(DEFVAR DP*PREDICATE.SET.ELEM NIL)
(DEFVAR DP*PREDICATE.SET.DELTA.SUBSET NIL)
(DEFVAR DP*PREDICATE.SET.DELTA.DELETE NIL)
(DEFVAR DP*PREDICATE.SET.<= NIL)
(DEFVAR DP*PREDICATE.SET.>= NIL)

(DEFVAR DP*PREDICATE.SET.DELTA.INTERSECTION.1 NIL)
(DEFVAR DP*PREDICATE.SET.DELTA.INTERSECTION.2 NIL)
(DEFVAR DP*PREDICATE.SET.DELTA.DIFFERENCE NIL)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;
;;;;;;;;;;;;;
;;;;;;;;;;;;; INTERFACE FUNCTIONS TO ACCESS THE PREDEFINED STRUCTURE SET
;;;;;;;;;;;;;
;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(DEFUN DP-SORT.SET (SET.SORT)
  ;;; Edited : 21.04.94 by CS
  ;;; Input  : a set sort
  ;;; Value  : the corresponding set sort
  
  (GETF DP*SORT.SET SET.SORT))


(DEFUN DP-SORT.ELEMENT.TYPE (SET.SORT)
  
  ;;; Edited : 21.04.94 by CS
  ;;; Input  : a set sort
  ;;; Value  : the corresponding element sort
  
  (GETF DP*SORT.ELEMENT.TYPE SET.SORT))


(DEFUN DP-FUNCTION.SET.EMPTY (SET.SORT)
  
  ;;; Edited : 21.04.94 by CS
  ;;; Input  : a set sort
  ;;; Value  : the corresponding constructor function empty
  
  (GETF DP*FUNCTION.SET.EMPTY SET.SORT))


(DEFUN DP-FUNCTION.SET.INSERT (SET.SORT)
  
  ;;; Edited : 21.04.94 by CS
  ;;; Input  : a set sort
  ;;; Value  : the corresponding constructor function insert
  
  (GETF DP*FUNCTION.SET.INSERT SET.SORT))


(DEFUN DP-FUNCTION.SET.ELEMENT (SET.SORT)
  
  ;;; Edited : 21.04.94 by CS
  ;;; Input  : a set sort
  ;;; Value  : the corresponding destructor function element
  
  (GETF DP*FUNCTION.SET.ELEMENT SET.SORT))


(DEFUN DP-FUNCTION.SET.SUBSET (SET.SORT)
  
  ;;; Edited : 21.04.94 by CS
  ;;; Input  : a set sort
  ;;; Value  : the corresponding destructor function subset
  
  (GETF DP*FUNCTION.SET.SUBSET SET.SORT))


(DEFUN DP-FUNCTION.SET.DELETE (SET.SORT)
  
  ;;; Edited : 21.04.94 by CS
  ;;; Input  : a set sort
  ;;; Value  : the corresponding function delete
  
  (GETF DP*FUNCTION.SET.DELETE SET.SORT))


(DEFUN DP-FUNCTION.SET.INTERSECTION (SET.SORT)
  ;;; Edited : 21.04.94 by CS
  ;;; Input  : a set sort
  ;;; Value  : the corresponding function intersection
  
  (GETF DP*FUNCTION.SET.INTERSECTION SET.SORT))

(DEFUN DP-FUNCTION.SET.DIFFERENCE (SET.SORT)
  ;;; Edited : 21.04.94 by CS
  ;;; Input  : a set sort
  ;;; Value  : the corresponding function difference
  
  (GETF DP*FUNCTION.SET.DIFFERENCE SET.SORT))


(DEFUN DP-FUNCTION.SET.UNION (SET.SORT)
  
  ;;; Edited : 21.04.94 by CS
  ;;; Input  : a set sort
  ;;; Value  : the corresponding function union
  
  (GETF DP*FUNCTION.SET.UNION SET.SORT))


(DEFUN DP-FUNCTION.SET.SYM.DIFFERENCE (SET.SORT)
  
  ;;; Edited : 21.04.94 by CS
  ;;; Input  : a set sort
  ;;; Value  : the corresponding function symetric difference
  
  (GETF DP*FUNCTION.SET.SYM.DIFFERENCE SET.SORT))


(DEFUN DP-PREDICATE.SET.ELEM (SET.SORT)
  
  ;;; Edited : 21.04.94 by CS
  ;;; Input  : a set sort
  ;;; Value  : the corresponding relation $\in$
  
  (GETF DP*PREDICATE.SET.ELEM SET.SORT))


(DEFUN DP-PREDICATE.SET.DELTA.SUBSET (SET.SORT)
  
  ;;; Edited : 21.04.94 by CS
  ;;; Input  : a set sort
  ;;; Value  : the corresponding delta difference predicate for subset
  
  (GETF DP*PREDICATE.SET.DELTA.SUBSET SET.SORT))


(DEFUN DP-PREDICATE.SET.DELTA.DELETE (SET.SORT)
  
  ;;; Edited : 21.04.94 by CS
  ;;; Input  : a set sort
  ;;; Value  : the corresponding delta difference predicate for delete
  
  (GETF DP*PREDICATE.SET.DELTA.DELETE SET.SORT))


(DEFUN DP-PREDICATE.SET.<= (SET.SORT)
  
  ;;; Edited : 21.04.94 by CS
  ;;; Input  : a set sort
  ;;; Value  : the corresponding relation $\subseteq$
  
  (GETF DP*PREDICATE.SET.<= SET.SORT))


(DEFUN DP-PREDICATE.SET.>= (SET.SORT)
  
  ;;; Edited : 21.04.94 by CS
  ;;; Input  : a set sort
  ;;; Value  : the corresponding relation $\supseteq$
  
  (GETF DP*PREDICATE.SET.>= SET.SORT))


(DEFUN DP-PREDICATE.SET.DELTA.INTERSECTION.1 (SET.SORT)
  
  ;;; Edited : 21.04.94 by CS
  ;;; Input  : a set sort
  ;;; Value  : the corresponding delta difference predicate for the first argument of intersection
  
  (GETF DP*PREDICATE.SET.DELTA.INTERSECTION.1 SET.SORT))


(DEFUN DP-PREDICATE.SET.DELTA.INTERSECTION.2 (SET.SORT)
  
  ;;; Edited : 21.04.94 by CS
  ;;; Input  : a set sort
  ;;; Value  : the corresponding delta difference predicate for the second argument of intersection
  
  (GETF DP*PREDICATE.SET.DELTA.INTERSECTION.2 SET.SORT))


(DEFUN DP-PREDICATE.SET.DELTA.DIFFERENCE (SET.SORT)
  
  ;;; Edited : 21.04.94 by CS
  ;;; Input  : a set sort
  ;;; Value  : the corresponding delta difference predicate for difference
  
  (GETF DP*PREDICATE.SET.DELTA.DIFFERENCE SET.SORT))



;;;;;================================================================================================
;;;;;
;;;;; Definition of datatype ARRAY:
;;;;;
;;;;;================================================================================================


(DEFVAR DP*ARRAY.NAMES (LIST "init" "default" "update" "index" "entry" "subarray" "select" "elem"))

(DEFVAR DP*ARRAY.CONSTRUCTOR.NAMES (LIST "init" "update"))

(DEFMACRO DP-ARRAY.NAMES ()
  
  ;;; Edited : 21.04.94 by CS
  ;;; Input  : none
  ;;; Value  : a list of strings denoting the predefined functions and predicates over arrays
  
  'DP*ARRAY.NAMES)


(DEFMACRO DP-ARRAY.CONSTRUCTOR.NAMES ()
  
  ;;; Edited : 21.04.94 by CS
  ;;; Input  : none
  ;;; Value  : a list of strings denoting the predefined constructor functions over arrays
  
  'DP*ARRAY.CONSTRUCTOR.NAMES)


(DEFUN DP-INSTANTIATE.ARRAY.SPEC
  (ARRAY.SORT INDEX.SORT ENTRY.SORT ARRAY.INIT ARRAY.DEFAULT ARRAY.UPDATE ARRAY.INDEX ARRAY.ENTRY ARRAY.SUBARRAY
	      ARRAY.SELECT)

  ;;; Edited : 21.04.94 by CS
  ;;; Input  : the names for the new array data type, its index sort, its entry sort, its constructor init with
  ;;;          its destructor default, its constructor update with its destructors index, entry, and subarray,
  ;;;          and its function select
  ;;; Value  : generates a string for the insertion of the following array specification (instantiated with
  ;;;          the above parameters):
  ;;;          .
  ;;;          .non-free structure
  ;;;          .      init(default:entry_type),
  ;;;          .      UPDATE(subarray:array, index:index_type,
  ;;;          .             entry:entry_type)
  ;;;          .      :array
  ;;;          .   {d-function select(array, index_type):entry_type {
  ;;;          .      axiom all i:index_type all x:entry_type
  ;;;          .         select(init(x), i) = x
  ;;;          .      axiom all i:index_type all x:entry_type
  ;;;          .            all A:array
  ;;;          .         select(update(A, i, x), i) = x
  ;;;          .      axiom all i,j:index_type all x:entry_type
  ;;;          .            all A:array
  ;;;          .            (not i = j) impl
  ;;;          .            select(update(A, j, x), i) =
  ;;;          .               select(A, i)}
  ;;;          .    axiom all A,B:array
  ;;;          .       (all i:index_type select(A, i) = select(B, i))
  ;;;          .          impl A = B }
  
  (LIST (LIST (LIST (FORMAT NIL "non-free structure ~A(~A:~A),"
			    ARRAY.INIT ARRAY.DEFAULT ENTRY.SORT)
		    (FORMAT NIL "   ~A(~A:~A, ~A:~A, ~A:~A):~A {"
			    ARRAY.UPDATE ARRAY.SUBARRAY ARRAY.SORT ARRAY.INDEX INDEX.SORT ARRAY.ENTRY ENTRY.SORT 
			    ARRAY.SORT)
		    (FORMAT NIL "   d-function ~A(~A, ~A):~A {"
			    ARRAY.SELECT ARRAY.SORT INDEX.SORT ENTRY.SORT)
		    (FORMAT NIL "      axiom all i:~A all x:~A"
			    INDEX.SORT ENTRY.SORT)
		    (FORMAT NIL "         ~A(~A(x), i) = x"
			    ARRAY.SELECT ARRAY.INIT)
		    (FORMAT NIL "      axiom all i:~A all x:~A all A:~A"
			    INDEX.SORT ENTRY.SORT ARRAY.SORT)
		    (FORMAT NIL "         ~A(~A(A, i, x), i) = x"
			    ARRAY.SELECT ARRAY.UPDATE)
		    (FORMAT NIL "      axiom all i,j:~A all x:~A all A:~A"
			    INDEX.SORT ENTRY.SORT ARRAY.SORT)
		    (FORMAT NIL "         (not i = j) impl ~A(~A(A, j, x), i) = ~A(A, i)"
			    ARRAY.SELECT ARRAY.UPDATE ARRAY.SELECT)
		    (FORMAT NIL "   }")
		    (FORMAT NIL "   axiom all A,B:~A"
			    ARRAY.SORT)
		    (FORMAT NIL "     (all i:~A ~A(A, i) = ~A(B, i)) impl A = B"
			    INDEX.SORT ARRAY.SELECT ARRAY.SELECT)
		    (FORMAT NIL "}")) nil)))


(DEFUN DP-INSTANTIATE.ARRAY.INPUT
  (ARRAY.SORT INDEX.SORT ENTRY.SORT ARRAY.INIT ARRAY.UPDATE ARRAY.DEFAULT ARRAY.INDEX ARRAY.ENTRY ARRAY.SUBARRAY
	      ARRAY.SELECT ARRAY.ELEM ARRAY.DELTA.SUBARRAY)

  ;;; Edited : 21.04.94 by CS
  ;;; Input  : the names for the new array data type, its index sort, its entry sort, its constructors init and update,
  ;;;          its destructors default, index, entry, and subarray, its function select, its $\in$ relation,
  ;;;          and its difference predicate for subarray
  ;;; Value  : generates a string for the insertion of the following specification of the predefined
  ;;;          array functions and predicates (instantiated with the above parameters) together with some
  ;;;          simplification lemmata:
  ;;;          .
  ;;;          .axiom all A:array all x:entry_type
  ;;;          .   A = init(x) impl A = init(default(A))
  ;;;          .
  ;;;          .axiom all x:entry_type
  ;;;          .   default(init(x)) = x
  ;;;          .
  ;;;          .axiom all A:array all i:index_type all x:entry_type
  ;;;          .   default(update(A, i, x)) = default(A)
  ;;;          .
  ;;;          .axiom all A,B:array all i:index_type all x:entry_type
  ;;;          .    (A = update(B, i, x) and not A = init(default(A)))
  ;;;          .      impl A = update(subarray(A), index(A), entry(A))
  ;;;          .
  ;;;          .axiom all A:array
  ;;;          .   A = update(subarray(A), index(A), entry(A))
  ;;;          .      impl not entry(A) = default(A)
  ;;;          .
  ;;;          .axiom all A:array
  ;;;          .   A = init(default(A)) impl subarray(A) = A
  ;;;          .
  ;;;          .axiom all A:array
  ;;;          .   A = update(subarray(A), index(A), entry(A))
  ;;;          .      impl select(subarray(A), index(A)) = default(A)
  ;;;          .
  ;;;          .a-predicate elem(i:index_type, A:array) = 
  ;;;          .   not select(A, i) = default(A)
  ;;; 	       .
  ;;;          .AXIOM all A:array
  ;;;          .   not (A = init(default(A)) and
  ;;;          .        A = update(subarray(A), index(A), entry(A)))
  ;;;          .
  ;;;          .a-predicate delta-subarray(A:array) = 
  ;;;          .   A = update(subarray(A), index(A), entry(A))
  ;;;          .
  ;;;          .axiom all A:array
  ;;;          .   default(init(default(A))) = default(A)
  ;;;          .
  ;;;          . axiom all A:array
  ;;;          .   index(update(subarray(A), index(A), entry(A))) =
  ;;;          .      index(A)
  ;;;          .
  ;;;          .axiom all A:array
  ;;;          .   entry(update(subarray(A), index(A), entry(A))) =
  ;;;          .      entry(A)
  ;;;          .
  ;;;          .axiom all A:array
  ;;;          .   subarray(update(subarray(A), index(A), entry(A))) =
  ;;;          .      subarray(A)

  (LIST (LIST (LIST (FORMAT NIL "axiom all A:~A all x:~A"
			    ARRAY.SORT ENTRY.SORT)
		    (FORMAT NIL "   A = ~A(x) impl A = ~A(~A(A))"
			    ARRAY.INIT ARRAY.INIT ARRAY.DEFAULT))
	      (LIST (LIST (FORMAT NIL "all A:~A all x:~A"
				  ARRAY.SORT ENTRY.SORT)
			  (FORMAT NIL "   A = ~A(x) impl A = ~A(~A(A))"
				  ARRAY.INIT ARRAY.INIT ARRAY.DEFAULT))))
	
	(LIST (LIST (FORMAT NIL "axiom all x:~A"
			    ENTRY.SORT)
		    (FORMAT NIL "   ~A(~A(x)) = x"
			    ARRAY.DEFAULT ARRAY.INIT))
	      (LIST (LIST (FORMAT NIL "all x:~A"
				  ENTRY.SORT)
			  (FORMAT NIL "   ~A(~A(x)) = x"
				  ARRAY.DEFAULT ARRAY.INIT))))
	
	(LIST (LIST (FORMAT NIL "axiom all A:~A all i:~A all x:~A"
			    ARRAY.SORT INDEX.SORT ENTRY.SORT)
		    (FORMAT NIL "   ~A(~A(A, i, x)) = ~A(A)"
			    ARRAY.DEFAULT ARRAY.UPDATE ARRAY.DEFAULT))
	      (LIST (LIST (FORMAT NIL "all A:~A all i:~A all x:~A"
				  ARRAY.SORT INDEX.SORT ENTRY.SORT)
			  (FORMAT NIL "   ~A(~A(A, i, x)) = ~A(A)"
				  ARRAY.DEFAULT ARRAY.UPDATE ARRAY.DEFAULT))))
	
	(LIST (LIST (FORMAT NIL "axiom all A,B:~A all i:~A all x:~A"
			    ARRAY.SORT INDEX.SORT ENTRY.SORT)
		    (FORMAT NIL "   (A = ~A(B, i, x) and not A = ~A(~A(A)))  impl A = ~A(~A(A), ~A(A), ~A(A))"
			    ARRAY.UPDATE ARRAY.INIT ARRAY.DEFAULT ARRAY.UPDATE ARRAY.SUBARRAY ARRAY.INDEX ARRAY.ENTRY))
	      (LIST (LIST (FORMAT NIL "all A,B:~A all i:~A all x:~A"
				  ARRAY.SORT INDEX.SORT ENTRY.SORT)
			  (FORMAT NIL "   (A = ~A(B, i, x) and not A = ~A(~A(A))) impl A = ~A(~A(A), ~A(A), ~A(A))"
				  ARRAY.UPDATE ARRAY.INIT ARRAY.DEFAULT ARRAY.UPDATE ARRAY.SUBARRAY ARRAY.INDEX ARRAY.ENTRY))))

	(LIST (LIST (FORMAT NIL "axiom all A:~A"
			    ARRAY.SORT)
		    (FORMAT NIL "   A = ~A(~A(A), ~A(A), ~A(A)) impl not ~A(A) = ~A(A)"
			    ARRAY.UPDATE ARRAY.SUBARRAY ARRAY.INDEX ARRAY.ENTRY ARRAY.ENTRY ARRAY.DEFAULT))
	      (LIST (LIST (FORMAT NIL "all A:~A"
				  ARRAY.SORT)
			  (FORMAT NIL "   A = ~A(~A(A), ~A(A), ~A(A)) impl not ~A(A) = ~A(A)"
				  ARRAY.UPDATE ARRAY.SUBARRAY ARRAY.INDEX ARRAY.ENTRY ARRAY.ENTRY ARRAY.DEFAULT))))

	(LIST (LIST (FORMAT NIL "axiom all A:~A"
			    ARRAY.SORT)
		    (FORMAT NIL "   A = ~A(~A(A)) impl ~A(A) = A"
			    ARRAY.INIT ARRAY.DEFAULT ARRAY.SUBARRAY))
	      (LIST (LIST (FORMAT NIL "all A:~A"
				  ARRAY.SORT)
			  (FORMAT NIL "   A = ~A(~A(A)) impl ~A(A) = A"
				  ARRAY.INIT ARRAY.DEFAULT ARRAY.SUBARRAY))))
	
	(LIST (LIST (FORMAT NIL "axiom all A:~A"
			    ARRAY.SORT)
		    (FORMAT NIL "   A = ~A(~A(A), ~A(A), ~A(A)) impl ~A(~A(A), ~A(A)) = ~A(A)"
			    ARRAY.UPDATE ARRAY.SUBARRAY ARRAY.INDEX ARRAY.ENTRY ARRAY.SELECT ARRAY.SUBARRAY ARRAY.INDEX
			    ARRAY.INDEX))
	      (LIST (LIST (FORMAT NIL "all A:~A"
				  ARRAY.SORT)
			  (FORMAT NIL "   A = ~A(~A(A), ~A(A), ~A(A)) impl ~A(~A(A), ~A(A)) = ~A(A)"
				  ARRAY.UPDATE ARRAY.SUBARRAY ARRAY.INDEX ARRAY.ENTRY ARRAY.SELECT ARRAY.SUBARRAY
				  ARRAY.INDEX ARRAY.DEFAULT))))
	
	(LIST (LIST (FORMAT NIL "a-predicate ~A(i:~A, A:~A) = "
			    ARRAY.ELEM INDEX.SORT ARRAY.SORT)
		    (FORMAT NIL "   not ~A(A, i) = ~A(A)"
			    ARRAY.SELECT ARRAY.DEFAULT)) nil)
	
					; und zum Beweisen:
	
	(LIST (LIST (FORMAT NIL "axiom all A:~A"
			    ARRAY.SORT)
		    (FORMAT NIL "   not (A = ~A(~A(A)) and A = ~A(~A(A), ~A(A), ~A(A)))"
			    ARRAY.INIT ARRAY.DEFAULT ARRAY.UPDATE ARRAY.SUBARRAY ARRAY.INDEX ARRAY.ENTRY))
	      (LIST (LIST (FORMAT NIL "all A:~A"
				  ARRAY.SORT)
			  (FORMAT NIL "   not (A = ~A(~A(A)) and A = ~A(~A(A), ~A(A), ~A(A)))"
				  ARRAY.INIT ARRAY.DEFAULT ARRAY.UPDATE ARRAY.SUBARRAY ARRAY.INDEX ARRAY.ENTRY))))
	
	(LIST (LIST (FORMAT NIL "a-predicate ~A(A:~A) = "
			    ARRAY.DELTA.SUBARRAY ARRAY.SORT)
		    (FORMAT NIL "   A = ~A(~A(A), ~A(A), ~A(A))"
			    ARRAY.UPDATE ARRAY.SUBARRAY ARRAY.INDEX ARRAY.ENTRY)) nil)

	(LIST (LIST (FORMAT NIL "axiom all A:~A"
			    ARRAY.SORT)
		    (FORMAT NIL "   ~A(~A(~A(A))) = ~A(A)"
			    ARRAY.DEFAULT ARRAY.INIT ARRAY.DEFAULT ARRAY.DEFAULT))
	      (LIST (LIST (FORMAT NIL "all A:~A"
				  ARRAY.SORT)
			  (FORMAT NIL "   ~A(~A(~A(A))) = ~A(A)"
				  ARRAY.DEFAULT ARRAY.INIT ARRAY.DEFAULT ARRAY.DEFAULT))))
	
	(LIST (LIST (FORMAT NIL "axiom all A:~A"
			    ARRAY.SORT)
		    (FORMAT NIL "   ~A(~A(~A(A), ~A(A), ~A(A))) = ~A(A)"
			    ARRAY.INDEX ARRAY.UPDATE ARRAY.SUBARRAY ARRAY.INDEX ARRAY.ENTRY ARRAY.INDEX))
	      (LIST (LIST (FORMAT NIL "axiom all A:~A"
				  ARRAY.SORT)
			  (FORMAT NIL "   ~A(~A(~A(A), ~A(A), ~A(A))) = ~A(A)"
				  ARRAY.INDEX ARRAY.UPDATE ARRAY.SUBARRAY ARRAY.INDEX ARRAY.ENTRY ARRAY.INDEX))))
	
	(LIST (LIST (FORMAT NIL "axiom all A:~A"
			    ARRAY.SORT)
		    (FORMAT NIL "   ~A(~A(~A(A), ~A(A), ~A(A))) = ~A(A)"
			    ARRAY.ENTRY ARRAY.UPDATE ARRAY.SUBARRAY ARRAY.INDEX ARRAY.ENTRY ARRAY.ENTRY))
	      (LIST (LIST (FORMAT NIL "axiom all A:~A"
				  ARRAY.SORT)
			  (FORMAT NIL "   ~A(~A(~A(A), ~A(A), ~A(A))) = ~A(A)"
				  ARRAY.ENTRY ARRAY.UPDATE ARRAY.SUBARRAY ARRAY.INDEX ARRAY.ENTRY ARRAY.ENTRY))))
	(LIST (LIST (FORMAT NIL "axiom all A:~A"
			    ARRAY.SORT)
		    (FORMAT NIL "   ~A(~A(~A(A), ~A(A), ~A(A))) = ~A(A)"
			    ARRAY.SUBARRAY ARRAY.UPDATE ARRAY.SUBARRAY ARRAY.INDEX ARRAY.ENTRY ARRAY.SUBARRAY))
	      (LIST (LIST (FORMAT NIL "axiom all A:~A"
				  ARRAY.SORT)
			  (FORMAT NIL "   ~A(~A(~A(A), ~A(A), ~A(A))) = ~A(A)"
				  ARRAY.SUBARRAY ARRAY.UPDATE ARRAY.SUBARRAY ARRAY.INDEX ARRAY.ENTRY ARRAY.SUBARRAY))))
	))

;;;;;================================================================================================
;;;;;
;;;;; ;;; Variables for the datatype ARRAY
;;;;;
;;;;;================================================================================================


(DEFVAR DP*SORT.ARRAY NIL)
(DEFVAR DP*SORT.INDEX.TYPE NIL)
(DEFVAR DP*SORT.ENTRY.TYPE NIL)

(DEFVAR DP*FUNCTION.ARRAY.INIT NIL)
(DEFVAR DP*FUNCTION.ARRAY.DEFAULT NIL)
(DEFVAR DP*FUNCTION.ARRAY.UPDATE NIL)
(DEFVAR DP*FUNCTION.ARRAY.INDEX NIL)
(DEFVAR DP*FUNCTION.ARRAY.ENTRY NIL)
(DEFVAR DP*FUNCTION.ARRAY.SUBARRAY NIL)
(DEFVAR DP*FUNCTION.ARRAY.SELECT NIL)

(DEFVAR DP*PREDICATE.ARRAY.ELEM NIL)
(DEFVAR DP*PREDICATE.ARRAY.DELTA.SUBARRAY NIL)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;
;;;;;;;;;;;;;
;;;;;;;;;;;;; INTERFACE FUNCTIONS TO ACCESS THE PREDEFINED STRUCTURE ARRAY
;;;;;;;;;;;;;
;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(DEFUN DP-SORT.ARRAY (ARRAY.SORT)

  ;;; Edited : 21.04.94 by CS
  ;;; Input  : an array sort
  ;;; Value  : the corresponding array sort
  
  (GETF DP*SORT.ARRAY ARRAY.SORT))


(DEFUN DP-SORT.INDEX.TYPE (ARRAY.SORT)

  ;;; Edited : 21.04.94 by CS
  ;;; Input  : an array sort
  ;;; Value  : the corresponding index sort
  
  (GETF DP*SORT.INDEX.TYPE ARRAY.SORT))


(DEFUN DP-SORT.ENTRY.TYPE (ARRAY.SORT)

  ;;; Edited : 21.04.94 by CS
  ;;; Input  : an array sort
  ;;; Value  : the corresponding entry sort
  
  (GETF DP*SORT.ENTRY.TYPE ARRAY.SORT))


(DEFUN DP-FUNCTION.ARRAY.INIT (ARRAY.SORT)
  ;;; Edited : 21.04.94 by CS
  ;;; Input  : an array sort
  ;;; Value  : the corresponding constructor function init
  
  (GETF DP*FUNCTION.ARRAY.INIT ARRAY.SORT))


(DEFUN DP-FUNCTION.ARRAY.DEFAULT (ARRAY.SORT)

  ;;; Edited : 21.04.94 by CS
  ;;; Input  : an array sort
  ;;; Value  : the corresponding destructor function default
  
  (GETF DP*FUNCTION.ARRAY.DEFAULT ARRAY.SORT))


(DEFUN DP-FUNCTION.ARRAY.UPDATE (ARRAY.SORT)

  ;;; Edited : 21.04.94 by CS
  ;;; Input  : an array sort
  ;;; Value  : the corresponding constructor function update
  
  (GETF DP*FUNCTION.ARRAY.UPDATE ARRAY.SORT))


(DEFUN DP-FUNCTION.ARRAY.INDEX (ARRAY.SORT)

  ;;; Edited : 21.04.94 by CS
  ;;; Input  : an array sort
  ;;; Value  : the corresponding destructor function index
  
  (GETF DP*FUNCTION.ARRAY.INDEX ARRAY.SORT))


(DEFUN DP-FUNCTION.ARRAY.ENTRY (ARRAY.SORT)

  ;;; Edited : 21.04.94 by CS
  ;;; Input  : an array sort
  ;;; Value  : the corresponding destructor function entry
  
  (GETF DP*FUNCTION.ARRAY.ENTRY ARRAY.SORT))


(DEFUN DP-FUNCTION.ARRAY.SUBARRAY (ARRAY.SORT)
  
  ;;; Edited : 21.04.94 by CS
  ;;; Input  : an array sort
  ;;; Value  : the corresponding destructor function subarray
  
  (GETF DP*FUNCTION.ARRAY.SUBARRAY ARRAY.SORT))


(DEFUN DP-FUNCTION.ARRAY.SELECT (ARRAY.SORT)

  ;;; Edited : 21.04.94 by CS
  ;;; Input  : an array sort
  ;;; Value  : the corresponding function select
  
  (GETF DP*FUNCTION.ARRAY.SELECT ARRAY.SORT))


(DEFUN DP-PREDICATE.ARRAY.ELEM (ARRAY.SORT)

  ;;; Edited : 21.04.94 by CS
  ;;; Input  : an array sort
  ;;; Value  : the corresponding $\in$ relation
  
  (GETF DP*PREDICATE.ARRAY.ELEM ARRAY.SORT))


(DEFUN DP-PREDICATE.ARRAY.DELTA.SUBARRAY (ARRAY.SORT)
  
  ;;; Edited : 21.04.94 by CS
  ;;; Input  : an array sort
  ;;; Value  : the corresponding delta difference predicate for subarray
  
  (GETF DP*PREDICATE.ARRAY.DELTA.SUBARRAY ARRAY.SORT))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;
;;;;;;;;;;;;;
;;;;;;;;;;;;; MAKING WFOS FOR THE PREDEFINED DATA STRUCTURES 
;;;;;;;;;;;;;
;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



(DEFUN DP=SIMPLE.INT.WFO.CREATE (VARIABLE REC.POS)
  
  ;;; edited : 25.03.93 by CS
  ;;; input  : a formal int variable and its recursive position in the slot "formal.parameters" of a function
  ;;; effect : creates a wfo.suggested for the simple integer induction ordering
  
  (LET* ((PRED1 (DA-TERM.CREATE (DP-FUNCTION.INT.MAKE_int) 
				(LIST (da-term.create (DP-FUNCTION.SIGN.+) nil)
				      (DA-TERM.CREATE (DP-FUNCTION.NAT.P)
						      (list (da-term.create (DP-FUNCTION.INT.ABS)
									    (list (da-term.create VARIABLE NIL))))))))
	 (PRED2 (DA-TERM.CREATE (DP-FUNCTION.INT.MAKE_INT)
				(LIST (da-term.create (DP-FUNCTION.SIGN.-) nil)
				      (DA-TERM.CREATE (DP-FUNCTION.NAT.P)
						      (list (da-term.create (DP-FUNCTION.INT.ABS)
									    (list (da-term.create VARIABLE NIL))))))))
	 (var (da-term.create variable nil))
	 (SIGN.LITS (DP=GENERATE.SIGN.LITS VARIABLE))
	 (ABS.LITS (DP=GENERATE.ABS.LITS VARIABLE)))
    (DA-WFO.SUGGESTED.CREATE
     (LIST REC.POS) NIL
     (DA-WFO.CREATE (LIST VAR)
		    (DA-WFO.TREE.CREATE
		     (LIST (CONS (DA-WFO.TREE.PRED.SET.CREATE NIL)
				 (LIST (FIRST ABS.LITS)))
			   (CONS (DA-WFO.TREE.CREATE
				  (LIST (CONS (DA-WFO.TREE.PRED.SET.CREATE (LIST (LIST VAR PRED1)))
					      (LIST (FIRST SIGN.LITS)))
					(CONS (DA-WFO.TREE.PRED.SET.CREATE (LIST (LIST VAR PRED2)))
					      (LIST (SECOND SIGN.LITS)))))
				 (LIST (SECOND ABS.LITS)))))
		    NIL (LIST VAR)))))


(DEFUN DP=GENERATE.SIGN.LITS (VARIABLE)
  
  ;;; edited : 26.03.93 by CS
  ;;; input  : a variable
  ;;; value  : a list consisting of two literals: sign(x) =/= +, sign(x) =/= -
  
  (LIST (DA-LITERAL.CREATE (DA-SIGN.MINUS) (DA-PREDICATE.EQUALITY)
			   (LIST (DA-TERM.CREATE (DP-FUNCTION.INT.SIGN) (LIST (DA-TERM.CREATE VARIABLE NIL)))
				 (DA-TERM.CREATE (DP-FUNCTION.SIGN.+) NIL)))
	(DA-LITERAL.CREATE (DA-SIGN.MINUS) (DA-PREDICATE.EQUALITY)
			   (LIST (DA-TERM.CREATE (DP-FUNCTION.INT.SIGN) (LIST (DA-TERM.CREATE VARIABLE NIL)))
																		  (DA-TERM.CREATE (DP-FUNCTION.SIGN.-) NIL)))))



(DEFUN DP=GENERATE.ABS.LITS (VARIABLE)
  
  ;;; edited : 26.03.93 by CS
  ;;; input  : a variable
  ;;; value  : a list consisting of two literals: abs(x) =/= 0, abs(x) =/= s(p(abs(x)))
  
  (LET* ((ABS.TERM (DA-TERM.CREATE (DP-FUNCTION.INT.ABS) (LIST (DA-TERM.CREATE VARIABLE NIL))))
	 (S.P.ABS (DA-TERM.CREATE (DP-FUNCTION.NAT.S) (LIST (DA-TERM.CREATE (DP-FUNCTION.NAT.P)
																							     (LIST (DA-TERM.COPY ABS.TERM)))))))
    (LIST (DA-LITERAL.CREATE (DA-SIGN.MINUS) (DA-PREDICATE.EQUALITY)
			     (LIST (DA-TERM.COPY ABS.TERM) (DA-TERM.CREATE (DP-FUNCTION.NAT.0) NIL)))
	  (DA-LITERAL.CREATE (DA-SIGN.MINUS) (DA-PREDICATE.EQUALITY)
			     (LIST ABS.TERM S.P.ABS)))))



(DEFUN DP=DIV.MOD.WFO.CREATE (VAR1 VAR2 REC.POSITIONS)
  
  ;;; edited : 25.03.93 by CS
  ;;; input  : a formal int variable and its recursive position in the slot "formal.parameters" of a function
  ;;; effect : creates a wfo.suggested for the simple integer induction ordering

  (LET* ((VAR1.ABS (DA-TERM.CREATE (DP-FUNCTION.INT.MAKE_INT)
				   (LIST (DA-TERM.CREATE (DP-FUNCTION.SIGN.+) NIL)
					 (DA-TERM.CREATE (DP-FUNCTION.INT.ABS) (LIST (DA-TERM.CREATE VAR1 NIL))))))
	 (VAR2.ABS (DA-TERM.CREATE (DP-FUNCTION.INT.MAKE_INT)
				   (LIST (DA-TERM.CREATE (DP-FUNCTION.SIGN.+) NIL)
					 (DA-TERM.CREATE (DP-FUNCTION.INT.ABS) (LIST (DA-TERM.CREATE VAR2 NIL))))))
	 (SUBST1 (UNI-TERMSUBST.CREATE.PARALLEL
		  (LIST (DA-TERM.CREATE VAR1 NIL) (DA-TERM.CREATE VAR2 NIL))
		  (LIST (DA-TERM.CREATE (DP-FUNCTION.INT.DIFF) (LIST (DA-TERM.COPY VAR1.ABS) (DA-TERM.COPY VAR2.ABS)))
			(DA-TERM.COPY VAR2.ABS))))
	 (SUBST2 (UNI-TERMSUBST.CREATE.PARALLEL
		  (LIST (DA-TERM.CREATE VAR1 NIL) (DA-TERM.CREATE VAR2 NIL))
		  (LIST (DA-TERM.CREATE (DP-FUNCTION.INT.DIFF) (LIST (DA-TERM.COPY VAR2.ABS) (DA-TERM.COPY VAR1.ABS)))
			(DA-TERM.COPY VAR2.ABS))))
	 (SIGN.LITS (DP=GENERATE.SIGN.LITS VAR1))
	 (ABS.LITS (DP=GENERATE.ABS.LITS VAR2))
	 (LE.LITS (LIST (DA-LITERAL.CREATE (DA-SIGN.MINUS) (DP-PREDICATE.INT.LE)
					   (LIST (DA-TERM.COPY VAR1.ABS) (DA-TERM.COPY VAR2.ABS)))
			(DA-LITERAL.CREATE (DA-SIGN.PLUS) (DP-PREDICATE.INT.LE)
					   (LIST VAR1.ABS VAR2.ABS))))
	 TREE FORM.PARS)
    
    (SETQ TREE (DA-WFO.TREE.CREATE
		(LIST (CONS (DA-WFO.TREE.PRED.SET.CREATE (LIST SUBST1))
			    (LIST (FIRST SIGN.LITS)))
		      (CONS (DA-WFO.TREE.PRED.SET.CREATE (LIST SUBST2))
			    (LIST (SECOND SIGN.LITS))))))
    (SETQ TREE (DA-WFO.TREE.CREATE
		(LIST (CONS (DA-WFO.TREE.PRED.SET.CREATE NIL)
			    (LIST (FIRST LE.LITS)))
		      (CONS TREE (LIST (SECOND LE.LITS))))))
    (SETQ TREE (DA-WFO.TREE.CREATE
		(LIST (CONS (DA-WFO.TREE.PRED.SET.CREATE NIL)
			    (LIST (FIRST ABS.LITS)))
		      (CONS TREE (LIST (SECOND ABS.LITS))))))
    (SETQ FORM.PARS (LIST (DA-TERM.CREATE VAR1 nil) (DA-TERM.CREATE VAR2 nil)))
    (DA-WFO.SUGGESTED.CREATE REC.POSITIONS NIL (DA-WFO.CREATE FORM.PARS TREE NIL FORM.PARS))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;
;;;;;;;;;;;;;
;;;;;;;;;;;;; INITIALIZING THE DATABASE WITH THE PREDEFINED DATA STRUCTURES
;;;;;;;;;;;;;
;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(DEFUN DP=INIT ()
  
  (DP=INTEGER.INIT))




(DEFUN DP=INTEGER.INIT ()
  
  ;;; edited : 17.02.93 by CS
  ;;; input  : none
  ;;; effect : calls DED-FORMULA.INSERT for each predefined object

  (MAPC #'(LAMBDA (FORMULA)
	    (DED-FORMULA.INSERT (CAR FORMULA) (SECOND FORMULA) 'PREDEFINED (MAKE-LIST (LENGTH (SECOND FORMULA)))))
	DP*INTEGER.INPUT)
  
  (SETQ DP*SORT.INT (DB-NAME.SORT "int"))
  (SETQ DP*SORT.SIGN (DB-NAME.SORT "sign"))
  (SETQ DP*SORT.NAT (DB-NAME.SORT "nat"))
  
  (SETQ DP*FUNCTION.SIGN.+ (DB-NAME.FUNCTION "+" NIL (DP-SORT.SIGN)))
  (SETQ DP*FUNCTION.SIGN.- (DB-NAME.FUNCTION "-" NIL (DP-SORT.SIGN)))
  
  
  (SETQ DP*FUNCTION.NAT.0 (DB-NAME.FUNCTION "0" NIL (DP-SORT.NAT)))
  (SETQ DP*FUNCTION.NAT.S (DB-NAME.FUNCTION "s" (LIST (DP-SORT.NAT)) (DP-SORT.NAT)))
  (SETQ DP*FUNCTION.NAT.P (DB-NAME.FUNCTION "p" (LIST (DP-SORT.NAT)) (DP-SORT.NAT)))
  
  (SETQ DP*FUNCTION.INT.MAKE_INT (DB-NAME.FUNCTION "make_int" (LIST (DP-SORT.SIGN) (DP-SORT.NAT)) (DP-SORT.INT)))
  (SETQ DP*FUNCTION.INT.SIGN (DB-NAME.FUNCTION "sign" (LIST (DP-SORT.INT)) (DP-SORT.SIGN)))
  (SETQ DP*FUNCTION.INT.ABS (DB-NAME.FUNCTION "abs" (LIST (DP-SORT.INT)) (DP-SORT.NAT)))
  (SETQ DP*FUNCTION.INT.SUCC (DB-NAME.FUNCTION "succ" (LIST (DP-SORT.INT)) (DP-SORT.INT)))
  (SETQ DP*FUNCTION.INT.PRED (DB-NAME.FUNCTION "pred" (LIST (DP-SORT.INT)) (DP-SORT.INT)))
  (SETQ DP*FUNCTION.INT.PLUS (DB-NAME.FUNCTION "+" (LIST (DP-SORT.INT) (DP-SORT.INT)) (DP-SORT.INT)))
  (SETQ DP*FUNCTION.INT.NULL (DB-NAME.FUNCTION "null" NIL (DP-SORT.INT)))
  
  (SETF (DA-PREFUN.WFO.SUGGESTED DP*FUNCTION.INT.PLUS)
	(list (DP=SIMPLE.INT.WFO.CREATE (FIRST (DA-PREFUN.FORMAL.PARAMETERS DP*FUNCTION.INT.PLUS)) 1)))
  (SETF (DA-PREFUN.REC.POSITIONS DP*FUNCTION.INT.PLUS) (LIST 1))
  (SETQ DP*FUNCTION.INT.DIFF (DB-NAME.FUNCTION "-" (LIST (DP-SORT.INT) (DP-SORT.INT)) (DP-SORT.INT)))
  
  (SETF (DA-PREFUN.WFO.SUGGESTED DP*FUNCTION.INT.DIFF)
	(list (DP=SIMPLE.INT.WFO.CREATE (FIRST (DA-PREFUN.FORMAL.PARAMETERS DP*FUNCTION.INT.DIFF)) 1)))
  (SETF (DA-PREFUN.REC.POSITIONS DP*FUNCTION.INT.DIFF) (LIST 1))
  
  (SETQ DP*FUNCTION.INT.NEG (DB-NAME.FUNCTION "-" (LIST (DP-SORT.INT)) (DP-SORT.INT)))
  (SETF (DA-PREFUN.WFO.SUGGESTED DP*FUNCTION.INT.NEG)
	(list (DP=SIMPLE.INT.WFO.CREATE (FIRST (DA-PREFUN.FORMAL.PARAMETERS DP*FUNCTION.INT.NEG)) 1)))
  (SETQ DP*PREDICATE.INT.LEQ (DB-NAME.PREDICATE "<=" (LIST (DP-SORT.INT) (DP-SORT.INT))))
  (SETQ DP*PREDICATE.INT.LE (DB-NAME.PREDICATE "<" (LIST (DP-SORT.INT) (DP-SORT.INT))))
  (SETQ DP*PREDICATE.INT.GE (DB-NAME.PREDICATE ">" (LIST (DP-SORT.INT) (DP-SORT.INT))))
  (SETQ DP*PREDICATE.INT.GEQ (DB-NAME.PREDICATE ">=" (LIST (DP-SORT.INT) (DP-SORT.INT))))
  (SETQ DP*FUNCTION.INT.DIV (DB-NAME.FUNCTION "div" (LIST (DP-SORT.INT) (DP-SORT.INT)) (DP-SORT.INT)))
  (SETF (DA-PREFUN.WFO.SUGGESTED DP*FUNCTION.INT.DIV)
	(list (DP=DIV.MOD.WFO.CREATE (FIRST (DA-PREFUN.FORMAL.PARAMETERS DP*FUNCTION.INT.DIV))
				     (SECOND (DA-PREFUN.FORMAL.PARAMETERS DP*FUNCTION.INT.DIV))
				     (LIST 1 2))))
  (SETF (DA-PREFUN.REC.POSITIONS DP*FUNCTION.INT.DIV) (LIST 1 2))
  (SETQ DP*FUNCTION.INT.MOD (DB-NAME.FUNCTION "mod" (LIST (DP-SORT.INT) (DP-SORT.INT)) (DP-SORT.INT)))
  (SETF (DA-PREFUN.WFO.SUGGESTED DP*FUNCTION.INT.MOD)
	(list (DP=DIV.MOD.WFO.CREATE (FIRST (DA-PREFUN.FORMAL.PARAMETERS DP*FUNCTION.INT.MOD))
				     (SECOND (DA-PREFUN.FORMAL.PARAMETERS DP*FUNCTION.INT.MOD))
				     (LIST 1 2))))
  (SETF (DA-PREFUN.REC.POSITIONS DP*FUNCTION.INT.MOD) (LIST 1 2))
  (SETQ DP*FUNCTION.INT.MULT (DB-NAME.FUNCTION "*" (LIST (DP-SORT.INT) (DP-SORT.INT)) (DP-SORT.INT)))
  (SETF (DA-PREFUN.WFO.SUGGESTED DP*FUNCTION.INT.MULT)
	(list (DP=SIMPLE.INT.WFO.CREATE (FIRST (DA-PREFUN.FORMAL.PARAMETERS DP*FUNCTION.INT.MULT)) 1)))
  (SETF (DA-PREFUN.REC.POSITIONS DP*FUNCTION.INT.MULT) (LIST 1))
  (SETF (DA-PREFUN.WFO.SUGGESTED DP*PREDICATE.INT.LEQ)
	(list (DP=SIMPLE.INT.WFO.CREATE (FIRST (DA-PREFUN.FORMAL.PARAMETERS DP*PREDICATE.INT.LEQ)) 1)))
  (SETF (DA-PREFUN.REC.POSITIONS DP*PREDICATE.INT.LEQ) (LIST 1))
  NIL)


(DEFUN DP-SET.INSTANTIATIONS (SET.SORT)
  ;;; Edited : 10.01.94 by CS
  ;;; Input  : the name for a set
  ;;; Value  : creates a list of instantiations, i.e., a list of triples (name new.name list)
  ;;;          denoting a mapping from the prefuns of set to the anticipated names
  ;;;          where list is a list of names of predefined prefuns which must be named different because
  ;;;          of overloading restrictions
  
  (LIST (LIST "empty" (DP=NAME.NO.CONSTRUCTOR.FUNCTION (FORMAT NIL "~A_empty" SET.SORT)) NIL)
	(LIST "insert" (DP=NAME.NO.CONSTRUCTOR.FUNCTION (FORMAT NIL "~A_insert" SET.SORT)) (LIST "delete"))
	(LIST "element" "element" NIL)
	(LIST "subset" "subset" NIL)
	(LIST "elem" "elem" NIL)
	(LIST "delete" "delete" (LIST "insert"))
	(LIST "+" "+" (LIST "*" "\\" "-"))
	(LIST "*" "*" (LIST "+" "\\" "-"))
	(LIST "\\" "\\" (LIST "+" "*" "-"))
	(LIST "-" "-" (LIST "+" "*" "\\"))
	(LIST "<=" "<=" NIL)
	(LIST ">=" ">=" NIL)))


(DEFUN DP-SET.INSTANTIATE (SET.SORT ELEMENT.SORT INSTANTIATION.LIST)
  
  ;;; edited : 10.01.94 by CS
  ;;; input  : the name of the set sort, the name of the element sort, and a list of instantiations
  ;;;          which maps the name of the predefined set object to the anticipated name of the object
  ;;; effect : calls DED-FORMULA.INSERT for each predefined object and inserts some
  ;;;          properties
  ;;; Value:   nil if the definition is ok, otherwise the first error message of ded-formula.insert.

  (LET* ((SET.EMPTY (DP=GET.NAME "empty" INSTANTIATION.LIST))
	 (SET.INSERT (DP=GET.NAME "insert" INSTANTIATION.LIST))
	 (SET.ELEMENT (DP=GET.NAME "element" INSTANTIATION.LIST))
	 (SET.SUBSET (DP=GET.NAME "subset" INSTANTIATION.LIST))
	 (SET.DELTA.SUBSET (FORMAT NIL "delta-~A" SET.SUBSET))
	 (SET.ELEM (DP=GET.NAME "elem" INSTANTIATION.LIST))
	 (SET.DELETE (DP=GET.NAME "delete" INSTANTIATION.LIST))
	 (SET.DELTA.DELETE (FORMAT NIL "delta-~A" SET.DELETE))
	 (SET.UNION (DP=GET.NAME "+" INSTANTIATION.LIST))
	 (SET.INTERSECTION (DP=GET.NAME "*" INSTANTIATION.LIST))
	 (SET.DIFFERENCE (DP=GET.NAME "\\" INSTANTIATION.LIST))
	 (SET.SYM.DIFFERENCE (DP=GET.NAME "-" INSTANTIATION.LIST))
	 (SET.<= (DP=GET.NAME "<=" INSTANTIATION.LIST))
	 (SET.>= (DP=GET.NAME ">=" INSTANTIATION.LIST))
	 (SET.DELTA.INTERSECTION.1 (FORMAT NIL "delta-~A-1" SET.INTERSECTION))
	 (SET.DELTA.INTERSECTION.2 (FORMAT NIL "delta-~A-2" SET.INTERSECTION))
	 (SET.DELTA.DIFFERENCE (FORMAT NIL "delta-~A-1" SET.DIFFERENCE))
	 SET.SORT.SYMBOL ERROR)
    
    (SOME #'(LAMBDA (FORMULA) 
	      (setq error (DED-FORMULA.INSERT (CAR FORMULA) (SECOND FORMULA) 'PREDEFINED)))
	  (DP-INSTANTIATE.SET.SPEC SET.SORT ELEMENT.SORT SET.EMPTY SET.INSERT SET.ELEMENT SET.SUBSET SET.ELEM))

    (Cond (Error)
	  (t (SETQ SET.SORT.SYMBOL (DB-NAME.SORT SET.SORT))
	     (SETQ DP*SORT.ELEMENT.TYPE (CONS SET.SORT.SYMBOL (CONS (DB-NAME.SORT ELEMENT.SORT) DP*SORT.ELEMENT.TYPE)))
	     (SETQ DP*SORT.SET (CONS SET.SORT.SYMBOL (CONS (DB-NAME.SORT SET.SORT) DP*SORT.SET)))
	     (SETF (GETF (DA-SORT.ATTRIBUTES (DP-SORT.SET SET.SORT.SYMBOL)) 'DISJUNCT.RANGE) T)
	     
	     (SETQ DP*FUNCTION.SET.EMPTY (CONS SET.SORT.SYMBOL (CONS (DB-NAME.FUNCTION SET.EMPTY NIL (DP-SORT.SET SET.SORT.SYMBOL))
								     DP*FUNCTION.SET.EMPTY)))
	     (SETQ DP*FUNCTION.SET.INSERT
		   (CONS SET.SORT.SYMBOL (CONS (DB-NAME.FUNCTION SET.INSERT (LIST (DP-SORT.ELEMENT.TYPE SET.SORT.SYMBOL) 
										  (DP-SORT.SET SET.SORT.SYMBOL))
								 (DP-SORT.SET SET.SORT.SYMBOL)) DP*FUNCTION.SET.INSERT)))
	     (SETQ DP*FUNCTION.SET.ELEMENT
		   (CONS SET.SORT.SYMBOL (CONS (DB-NAME.FUNCTION SET.ELEMENT
								 (LIST (DP-SORT.SET SET.SORT.SYMBOL)) (DP-SORT.ELEMENT.TYPE SET.SORT.SYMBOL))
					       DP*FUNCTION.SET.ELEMENT)))
	     (SETQ DP*FUNCTION.SET.SUBSET
		   (CONS SET.SORT.SYMBOL (CONS (DB-NAME.FUNCTION SET.SUBSET (LIST (DP-SORT.SET SET.SORT.SYMBOL)) (DP-SORT.SET SET.SORT.SYMBOL))
					       DP*FUNCTION.SET.SUBSET)))
	     (SETQ DP*PREDICATE.SET.ELEM
		   (CONS SET.SORT.SYMBOL (CONS (DB-NAME.PREDICATE SET.ELEM
						  (LIST (DP-SORT.ELEMENT.TYPE SET.SORT.SYMBOL) (DP-SORT.SET SET.SORT.SYMBOL)))
					       DP*PREDICATE.SET.ELEM)))
	     (SETF (DA-PREFUN.WFO.SUGGESTED (DP-PREDICATE.SET.ELEM SET.SORT.SYMBOL))
		   (list (DA-WFO.CREATE.STRUCTURAL
			  (DA-TERM.CREATE (SECOND (DA-PREFUN.FORMAL.PARAMETERS (DP-PREDICATE.SET.ELEM SET.SORT.SYMBOL))))
			  2)))
	     
	     (SETF (DA-PREFUN.LISPFCT (DP-FUNCTION.SET.SUBSET SET.SORT.SYMBOL)) 'EG=EVAL.SET.SUBSET)
	     (SETF (DA-PREFUN.LISPFCT (DP-FUNCTION.SET.ELEMENT SET.SORT.SYMBOL)) 'EG=EVAL.SET.ELEMENT)
	     
	     (SETF (DA-PREFUN.LISPFCT (DP-PREDICATE.SET.ELEM SET.SORT.SYMBOL)) 'EG=EVAL.SET.ELEM)
    
	     (some #'(LAMBDA (FORMULA) 
		       (setq error (DED-FORMULA.INSERT (CAR FORMULA) (SECOND FORMULA) 'PREDEFINED)))
		   (DP-INSTANTIATE.SET.INPUT SET.SORT ELEMENT.SORT SET.EMPTY SET.INSERT SET.ELEMENT SET.SUBSET SET.DELTA.SUBSET
					     SET.ELEM SET.DELETE SET.DELTA.DELETE SET.UNION SET.INTERSECTION SET.DIFFERENCE
					     SET.SYM.DIFFERENCE SET.<= SET.>= SET.DELTA.INTERSECTION.1
					     SET.DELTA.INTERSECTION.2 SET.DELTA.DIFFERENCE))
	     (cond (error)
		   (t 	     
		    (SETQ DP*PREDICATE.SET.DELTA.SUBSET
			  (CONS SET.SORT.SYMBOL (CONS (DB-NAME.PREDICATE SET.DELTA.SUBSET (LIST (DP-SORT.SET SET.SORT.SYMBOL)))
						      DP*PREDICATE.SET.DELTA.SUBSET)))
		    (SETF (DA-FUNCTION.ARG.LIMITED (DP-FUNCTION.SET.SUBSET SET.SORT.SYMBOL))
			  (LIST (LIST 1 (DP-PREDICATE.SET.DELTA.SUBSET SET.SORT.SYMBOL))))
		    
		    (SETQ DP*FUNCTION.SET.DELETE
			  (CONS SET.SORT.SYMBOL (CONS (DB-NAME.FUNCTION SET.DELETE
									(LIST (DP-SORT.ELEMENT.TYPE SET.SORT.SYMBOL) (DP-SORT.SET SET.SORT.SYMBOL))
									(DP-SORT.SET SET.SORT.SYMBOL))
						      DP*FUNCTION.SET.DELETE)))
		    (SETF (DA-PREFUN.WFO.SUGGESTED (DP-FUNCTION.SET.DELETE SET.SORT.SYMBOL))
			  (list (DA-WFO.CREATE.STRUCTURAL
				 (DA-TERM.CREATE (SECOND (DA-PREFUN.FORMAL.PARAMETERS (DP-FUNCTION.SET.DELETE SET.SORT.SYMBOL)))) 2)))
		    (SETQ DP*PREDICATE.SET.DELTA.DELETE
			  (CONS SET.SORT.SYMBOL (CONS (DB-NAME.PREDICATE SET.DELTA.DELETE
									 (LIST (DP-SORT.ELEMENT.TYPE SET.SORT.SYMBOL)
									       (DP-SORT.SET SET.SORT.SYMBOL)))
						      DP*PREDICATE.SET.DELTA.DELETE)))
		    (SETF (DA-FUNCTION.ARG.LIMITED (DP-FUNCTION.SET.DELETE SET.SORT.SYMBOL))
			  (LIST (LIST 2 (DP-PREDICATE.SET.DELTA.DELETE SET.SORT.SYMBOL))))
		    
		    (SETQ DP*FUNCTION.SET.UNION
			  (CONS SET.SORT.SYMBOL (CONS (DB-NAME.FUNCTION SET.UNION (LIST (DP-SORT.SET SET.SORT.SYMBOL)
											(DP-SORT.SET SET.SORT.SYMBOL))
									(DP-SORT.SET SET.SORT.SYMBOL))
						      DP*FUNCTION.SET.UNION)))
		    (SETF (DA-PREFUN.WFO.SUGGESTED (DP-FUNCTION.SET.UNION SET.SORT.SYMBOL))
			  (list (DA-WFO.CREATE.STRUCTURAL
				 (DA-TERM.CREATE (FIRST (DA-PREFUN.FORMAL.PARAMETERS (DP-FUNCTION.SET.UNION SET.SORT.SYMBOL)))) 1)))
		    (SETQ DP*FUNCTION.SET.INTERSECTION
			  (CONS SET.SORT.SYMBOL (CONS (DB-NAME.FUNCTION SET.INTERSECTION (LIST (DP-SORT.SET SET.SORT.SYMBOL) 
											       (DP-SORT.SET SET.SORT.SYMBOL))
									(DP-SORT.SET SET.SORT.SYMBOL))
						      DP*FUNCTION.SET.INTERSECTION)))
		    (SETF (DA-PREFUN.WFO.SUGGESTED (DP-FUNCTION.SET.INTERSECTION SET.SORT.SYMBOL))
			  (list (DA-WFO.CREATE.STRUCTURAL
				 (DA-TERM.CREATE (FIRST (DA-PREFUN.FORMAL.PARAMETERS (DP-FUNCTION.SET.INTERSECTION SET.SORT.SYMBOL))))
				 1)))
		    (SETQ DP*FUNCTION.SET.DIFFERENCE
			  (CONS SET.SORT.SYMBOL (CONS (DB-NAME.FUNCTION SET.DIFFERENCE (LIST (DP-SORT.SET SET.SORT.SYMBOL) 
											     (DP-SORT.SET SET.SORT.SYMBOL))
									(DP-SORT.SET SET.SORT.SYMBOL))
						      DP*FUNCTION.SET.DIFFERENCE)))
		    (SETF (DA-PREFUN.WFO.SUGGESTED (DP-FUNCTION.SET.DIFFERENCE SET.SORT.SYMBOL))
			  (list (DA-WFO.CREATE.STRUCTURAL
				 (DA-TERM.CREATE (FIRST (DA-PREFUN.FORMAL.PARAMETERS (DP-FUNCTION.SET.DIFFERENCE SET.SORT.SYMBOL))))
				 1)))
		    (SETQ DP*FUNCTION.SET.SYM.DIFFERENCE
			  (CONS SET.SORT.SYMBOL (CONS (DB-NAME.FUNCTION SET.SYM.DIFFERENCE
									(LIST (DP-SORT.SET SET.SORT.SYMBOL) 
									      (DP-SORT.SET SET.SORT.SYMBOL))
									(DP-SORT.SET SET.SORT.SYMBOL))
						      DP*FUNCTION.SET.SYM.DIFFERENCE)))
		    (SETQ DP*PREDICATE.SET.<=
			  (CONS SET.SORT.SYMBOL (CONS (DB-NAME.PREDICATE SET.<= (LIST (DP-SORT.SET SET.SORT.SYMBOL) 
										      (DP-SORT.SET SET.SORT.SYMBOL)))
						      DP*PREDICATE.SET.<=)))
		    (SETQ DP*PREDICATE.SET.>=
			  (CONS SET.SORT.SYMBOL (CONS (DB-NAME.PREDICATE SET.>=
									 (LIST (DP-SORT.SET SET.SORT.SYMBOL) 
									       (DP-SORT.SET SET.SORT.SYMBOL)))
						      DP*PREDICATE.SET.>=)))
		    (SETQ DP*PREDICATE.SET.DELTA.INTERSECTION.1
			  (CONS SET.SORT.SYMBOL (CONS (DB-NAME.PREDICATE SET.DELTA.INTERSECTION.1
								  (LIST (DP-SORT.SET SET.SORT.SYMBOL) 
									(DP-SORT.SET SET.SORT.SYMBOL)))
						      DP*PREDICATE.SET.DELTA.INTERSECTION.1)))
		    (SETF (DA-PREFUN.WFO.SUGGESTED (DP-PREDICATE.SET.DELTA.INTERSECTION.1 SET.SORT.SYMBOL))
			  (list (DA-WFO.CREATE.STRUCTURAL
			  (DA-TERM.CREATE (FIRST (DA-PREFUN.FORMAL.PARAMETERS (DP-PREDICATE.SET.DELTA.INTERSECTION.1 SET.SORT.SYMBOL))))
			  1)))
		    (SETQ DP*PREDICATE.SET.DELTA.INTERSECTION.2
			  (CONS SET.SORT.SYMBOL (CONS (DB-NAME.PREDICATE SET.DELTA.INTERSECTION.2
									 (LIST (DP-SORT.SET SET.SORT.SYMBOL) 
									       (DP-SORT.SET SET.SORT.SYMBOL)))
						      DP*PREDICATE.SET.DELTA.INTERSECTION.2)))
		    (SETF (DA-PREFUN.WFO.SUGGESTED (DP-PREDICATE.SET.DELTA.INTERSECTION.2 SET.SORT.SYMBOL))
			  (list (DA-WFO.CREATE.STRUCTURAL
				 (DA-TERM.CREATE (SECOND (DA-PREFUN.FORMAL.PARAMETERS (DP-PREDICATE.SET.DELTA.INTERSECTION.2 SET.SORT.SYMBOL)))) 2)))
		    (SETF (DA-FUNCTION.ARG.LIMITED (DP-FUNCTION.SET.INTERSECTION SET.SORT.SYMBOL))
			  (LIST (LIST 1 (DP-PREDICATE.SET.DELTA.INTERSECTION.1 SET.SORT.SYMBOL))
				(LIST 2 (DP-PREDICATE.SET.DELTA.INTERSECTION.2 SET.SORT.SYMBOL))))
		    
		    (SETQ DP*PREDICATE.SET.DELTA.DIFFERENCE
			  (CONS SET.SORT.SYMBOL (CONS (DB-NAME.PREDICATE SET.DELTA.DIFFERENCE
									 (LIST (DP-SORT.SET SET.SORT.SYMBOL) (DP-SORT.SET SET.SORT.SYMBOL)))
						      DP*PREDICATE.SET.DELTA.DIFFERENCE)))
		    (SETF (DA-PREFUN.WFO.SUGGESTED (DP-PREDICATE.SET.DELTA.DIFFERENCE SET.SORT.SYMBOL))
			  (list (DA-WFO.CREATE.STRUCTURAL
			  (DA-TERM.CREATE (FIRST (DA-PREFUN.FORMAL.PARAMETERS (DP-PREDICATE.SET.DELTA.DIFFERENCE SET.SORT.SYMBOL)))) 1)))
		    (SETF (DA-FUNCTION.ARG.LIMITED (DP-FUNCTION.SET.DIFFERENCE SET.SORT.SYMBOL))
			  (LIST (LIST 1 (DP-PREDICATE.SET.DELTA.DIFFERENCE SET.SORT.SYMBOL))))
		    
		    (SETF (DA-PREFUN.LISPFCT (DP-FUNCTION.SET.DELETE SET.SORT.SYMBOL)) 'EG=EVAL.SET.DELETE)
		    (SETF (DA-PREFUN.LISPFCT (DP-FUNCTION.SET.UNION SET.SORT.SYMBOL)) 'EG=EVAL.SET.UNION)
		    (SETF (DA-PREFUN.LISPFCT (DP-FUNCTION.SET.INTERSECTION SET.SORT.SYMBOL)) 'EG=EVAL.SET.INTERSECTION)
		    (SETF (DA-PREFUN.LISPFCT (DP-FUNCTION.SET.DIFFERENCE SET.SORT.SYMBOL)) 'EG=EVAL.SET.DIFFERENCE)
		    (SETF (DA-PREFUN.LISPFCT (DP-FUNCTION.SET.SYM.DIFFERENCE SET.SORT.SYMBOL)) 'EG=EVAL.SET.SYM.DIFFERENCE)
		    
		    (SETF (DA-PREFUN.LISPFCT (DP-PREDICATE.SET.<= SET.SORT.SYMBOL)) 'EG=EVAL.SET.<=)
		    (SETF (DA-PREFUN.LISPFCT (DP-PREDICATE.SET.>= SET.SORT.SYMBOL)) 'EG=EVAL.SET.>=)
		    (SETF (DA-PREFUN.LISPFCT (DP-PREDICATE.SET.DELTA.SUBSET SET.SORT.SYMBOL)) 'EG=EVAL.SET.DELTA.SUBSET)
		    (SETF (DA-PREFUN.LISPFCT (DP-PREDICATE.SET.DELTA.DELETE SET.SORT.SYMBOL)) 'EG=EVAL.SET.DELTA.DELETE)
		    (SETF (DA-PREFUN.LISPFCT (DP-PREDICATE.SET.DELTA.INTERSECTION.1 SET.SORT.SYMBOL)) 'EG=EVAL.SET.DELTA.INTERSECTION.1)
		    (SETF (DA-PREFUN.LISPFCT (DP-PREDICATE.SET.DELTA.INTERSECTION.2 SET.SORT.SYMBOL)) 'EG=EVAL.SET.DELTA.INTERSECTION.2)
		    (SETF (DA-PREFUN.LISPFCT (DP-PREDICATE.SET.DELTA.DIFFERENCE SET.SORT.SYMBOL)) 'EG=EVAL.SET.DELTA.DIFFERENCE)
		    
		    nil))))))


(DEFUN DP-ARRAY.INSTANTIATIONS (ARRAY.SORT)
  
  ;;; Edited : 10.01.94 by CS
  ;;; Input  : the name for an array
  ;;; Value  : creates a list of instantiations, i.e., a list of triples (name new.name list)
  ;;;          denoting a mapping from the prefuns of array to the anticipated names
  ;;;          where list is a list of names of predefined prefuns which must be named different because
  ;;;          of overloading restrictions
  
  (LIST (LIST "init" (DP=NAME.NO.CONSTRUCTOR.FUNCTION (FORMAT NIL "~A_init" ARRAY.SORT)) NIL)
	(LIST "update" (DP=NAME.NO.CONSTRUCTOR.FUNCTION (FORMAT NIL "~A_update" ARRAY.SORT)) NIL)
	(LIST "default" "default" NIL)
	(LIST "index" "index" NIL)
	(LIST "entry" "entry" NIL)
	(LIST "subarray" "subarray" NIL)
	(LIST "select" "select" NIL)
	(LIST "elem" "elem" NIL)))


(DEFUN DP-ARRAY.INSTANTIATE (ARRAY.SORT INDEX.SORT ENTRY.SORT INSTANTIATION.LIST)
  
  ;;; edited : 10.01.94 by CS
  ;;; input  : the name of the array sort, the name of the index sort, the name of the entry sort, 
  ;;;          and a list of instantiations which maps the name of the predefined arryy object to the
  ;;;          anticipated name of the object
  ;;; effect : calls DED-FORMULA.INSERT for each predefined object and inserts some
  ;;;          properties

  (LET* ((ARRAY.INIT (DP=GET.NAME "init" INSTANTIATION.LIST))
	 (ARRAY.UPDATE (DP=GET.NAME "update" INSTANTIATION.LIST))
	 (ARRAY.DEFAULT (DP=GET.NAME "default" INSTANTIATION.LIST))
	 (ARRAY.INDEX (DP=GET.NAME "index" INSTANTIATION.LIST))
	 (ARRAY.ENTRY (DP=GET.NAME "entry" INSTANTIATION.LIST))
	 (ARRAY.SUBARRAY (DP=GET.NAME "subarray" INSTANTIATION.LIST))
	 (ARRAY.SELECT (DP=GET.NAME "select" INSTANTIATION.LIST))
	 (ARRAY.ELEM (DP=GET.NAME "elem" INSTANTIATION.LIST))
	 (ARRAY.DELTA.SUBARRAY (FORMAT NIL "delta-~A" ARRAY.SUBARRAY))
	 ARRAY.SORT.SYMBOL Error)
    
    (SOME #'(LAMBDA (FORMULA) 
	      (setq error (DED-FORMULA.INSERT (CAR FORMULA) (SECOND FORMULA) 'PREDEFINED)))
	  (DP-INSTANTIATE.ARRAY.SPEC ARRAY.SORT INDEX.SORT ENTRY.SORT ARRAY.INIT ARRAY.DEFAULT ARRAY.UPDATE ARRAY.INDEX
				     ARRAY.ENTRY ARRAY.SUBARRAY ARRAY.SELECT))
    
    (cond (error)
	  (t (SETQ ARRAY.SORT.SYMBOL (DB-NAME.SORT ARRAY.SORT))
	     
	     (SETQ DP*SORT.INDEX.TYPE (CONS ARRAY.SORT.SYMBOL (CONS (DB-NAME.SORT INDEX.SORT) DP*SORT.INDEX.TYPE)))
	     (SETQ DP*SORT.ENTRY.TYPE (CONS ARRAY.SORT.SYMBOL (CONS (DB-NAME.SORT ENTRY.SORT) DP*SORT.ENTRY.TYPE)))
	     (SETQ DP*SORT.ARRAY (CONS ARRAY.SORT.SYMBOL (CONS (DB-NAME.SORT ARRAY.SORT) DP*SORT.ARRAY)))
	     
	     (SETQ DP*FUNCTION.ARRAY.INIT (CONS ARRAY.SORT.SYMBOL
						(CONS (DB-NAME.FUNCTION ARRAY.INIT (LIST (DP-SORT.ENTRY.TYPE ARRAY.SORT.SYMBOL))
									(DP-SORT.ARRAY ARRAY.SORT.SYMBOL))
						      DP*FUNCTION.ARRAY.INIT)))
	     (SETQ DP*FUNCTION.ARRAY.DEFAULT (CONS ARRAY.SORT.SYMBOL
						   (CONS (DB-NAME.FUNCTION ARRAY.DEFAULT
									   (LIST (DP-SORT.ARRAY ARRAY.SORT.SYMBOL))
									   (DP-SORT.ENTRY.TYPE ARRAY.SORT.SYMBOL))
							 DP*FUNCTION.ARRAY.DEFAULT)))
	     (SETQ DP*FUNCTION.ARRAY.UPDATE (CONS ARRAY.SORT.SYMBOL
						  (CONS (DB-NAME.FUNCTION ARRAY.UPDATE
									  (LIST (DP-SORT.ARRAY ARRAY.SORT.SYMBOL)
										(DP-SORT.INDEX.TYPE ARRAY.SORT.SYMBOL)
										(DP-SORT.ENTRY.TYPE ARRAY.SORT.SYMBOL))
									  (DP-SORT.ARRAY ARRAY.SORT.SYMBOL))
							DP*FUNCTION.ARRAY.UPDATE)))
	     (SETQ DP*FUNCTION.ARRAY.INDEX (CONS ARRAY.SORT.SYMBOL
						 (CONS (DB-NAME.FUNCTION ARRAY.INDEX
									 (LIST (DP-SORT.ARRAY ARRAY.SORT.SYMBOL))
									 (DP-SORT.INDEX.TYPE ARRAY.SORT.SYMBOL))
						       DP*FUNCTION.ARRAY.INDEX)))
	     (SETQ DP*FUNCTION.ARRAY.ENTRY (CONS ARRAY.SORT.SYMBOL
						 (CONS (DB-NAME.FUNCTION ARRAY.ENTRY
									 (LIST (DP-SORT.ARRAY ARRAY.SORT.SYMBOL))
									 (DP-SORT.ENTRY.TYPE ARRAY.SORT.SYMBOL))
						       DP*FUNCTION.ARRAY.ENTRY)))
	     (SETQ DP*FUNCTION.ARRAY.SUBARRAY (CONS ARRAY.SORT.SYMBOL
						    (CONS (DB-NAME.FUNCTION ARRAY.SUBARRAY
									    (LIST (DP-SORT.ARRAY ARRAY.SORT.SYMBOL))
									    (DP-SORT.ARRAY ARRAY.SORT.SYMBOL))
							  DP*FUNCTION.ARRAY.SUBARRAY)))
	     (SETQ DP*FUNCTION.ARRAY.SELECT (CONS ARRAY.SORT.SYMBOL
						  (CONS (DB-NAME.FUNCTION ARRAY.SELECT
									  (LIST (DP-SORT.ARRAY ARRAY.SORT.SYMBOL)
										(DP-SORT.INDEX.TYPE ARRAY.SORT.SYMBOL))
									  (DP-SORT.ENTRY.TYPE ARRAY.SORT.SYMBOL))
							DP*FUNCTION.ARRAY.SELECT)))
	     (SETF (DA-PREFUN.WFO.SUGGESTED (DP-FUNCTION.ARRAY.SELECT ARRAY.SORT.SYMBOL))
		   (list (DA-WFO.CREATE.STRUCTURAL 
			  (DA-TERM.CREATE (FIRST (DA-PREFUN.FORMAL.PARAMETERS (DP-FUNCTION.ARRAY.SELECT ARRAY.SORT.SYMBOL))))
						   1))) ;; hier
	     
	     (SETF (DA-PREFUN.LISPFCT (DP-FUNCTION.ARRAY.DEFAULT ARRAY.SORT.SYMBOL)) 'EG=EVAL.ARRAY.DEFAULT)
	     (SETF (DA-PREFUN.LISPFCT (DP-FUNCTION.ARRAY.INDEX ARRAY.SORT.SYMBOL)) 'EG=EVAL.ARRAY.INDEX)
	     (SETF (DA-PREFUN.LISPFCT (DP-FUNCTION.ARRAY.ENTRY ARRAY.SORT.SYMBOL)) 'EG=EVAL.ARRAY.ENTRY)
	     (SETF (DA-PREFUN.LISPFCT (DP-FUNCTION.ARRAY.SUBARRAY ARRAY.SORT.SYMBOL)) 'EG=EVAL.ARRAY.SUBARRAY)
	     (SETF (DA-PREFUN.LISPFCT (DP-FUNCTION.ARRAY.SELECT ARRAY.SORT.SYMBOL)) 'EG=EVAL.ARRAY.SELECT)
	     
	     (SOME #'(LAMBDA (FORMULA) (setq error (DED-FORMULA.INSERT (CAR FORMULA) (SECOND FORMULA) 'PREDEFINED)))
		   (DP-INSTANTIATE.ARRAY.INPUT ARRAY.SORT INDEX.SORT ENTRY.SORT ARRAY.INIT ARRAY.UPDATE ARRAY.DEFAULT ARRAY.INDEX
					       ARRAY.ENTRY ARRAY.SUBARRAY ARRAY.SELECT ARRAY.ELEM ARRAY.DELTA.SUBARRAY))
	     
	     (cond (error)
		   (t 
		    (SETQ DP*PREDICATE.ARRAY.ELEM (CONS ARRAY.SORT.SYMBOL
							(CONS (DB-NAME.PREDICATE ARRAY.ELEM
										 (LIST (DP-SORT.INDEX.TYPE ARRAY.SORT.SYMBOL)
										       (DP-SORT.ARRAY ARRAY.SORT.SYMBOL)))
							      DP*PREDICATE.ARRAY.ELEM)))
		    (SETQ DP*PREDICATE.ARRAY.DELTA.SUBARRAY (CONS ARRAY.SORT.SYMBOL
								  (CONS (DB-NAME.PREDICATE ARRAY.DELTA.SUBARRAY
											   (LIST (DP-SORT.ARRAY ARRAY.SORT.SYMBOL)))
									DP*PREDICATE.ARRAY.DELTA.SUBARRAY)))
		    (SETF (DA-FUNCTION.ARG.LIMITED (DP-FUNCTION.ARRAY.SUBARRAY ARRAY.SORT.SYMBOL))
			  (LIST (LIST 1 (DP-PREDICATE.ARRAY.DELTA.SUBARRAY ARRAY.SORT.SYMBOL))))
		    
		    (SETF (DA-PREFUN.LISPFCT (DP-PREDICATE.ARRAY.ELEM ARRAY.SORT.SYMBOL)) 'EG=EVAL.ARRAY.ELEM)
		    (SETF (DA-PREFUN.LISPFCT (DP-PREDICATE.ARRAY.DELTA.SUBARRAY ARRAY.SORT.SYMBOL)) 'EG=EVAL.ARRAY.DELTA.SUBARRAY)
		    nil))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; DP stuff
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



(DEFUN DP=GET.NAME (NAME INSTANTIATIONS)
  
  ;;; Edited : 10.01.94 by CS
  ;;; Input  : a string and a list of instantiations, i.e., a list of triples (list name new.name T/NIL)
  ;;; Value  : looks up in INSTANTIATIONS for the new name of NAME
  
  (SECOND (FIND-IF #'(LAMBDA (INSTANCE) (STRING-EQUAL NAME (FIRST INSTANCE)))
			     INSTANTIATIONS)))


(DEFUN DP=NAME.NO.CONSTRUCTOR.FUNCTION (NAME)
  
  ;;; Edited : 10.01.94 by CS
  ;;; Input  : a string
  ;;; Value  : a prefun is to be defined, the anticipated name is NAME, however, due to overloading
  ;;;          restrictions it may be possible that the anticipated name is not possible, in this
  ;;;          case a new name is generated and this function is recursively called for the newly
  ;;;          generated name
  
  (COND ((SOME #'(LAMBDA (OBJECT)
		   (AND (DA-FUNCTION.IS OBJECT)
			(DA-FUNCTION.IS.CONSTRUCTOR OBJECT)))
	       (DB-NAME.OBJECT NAME))
	 (DP=NAME.NO.CONSTRUCTOR.FUNCTION (FORMAT NIL "~A'" NAME)))
	(T NAME)))





;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                                                                                                                      ;;;
;;;                                         SET PROVER                                                                   ;;;
;;;                                                                                                                      ;;;
;;;                due to L. Hines: Strive: The strive-based subset prover                                               ;;;
;;;                                 in: 10th CADE, Springer Verlag, 1990                                                 ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(DEFVAR DP*SET.REDUCE.LIMIT 5)
(DEFVAR DP*SET.REDUCE.ACTUAL 0)
(DEFVAR DP*SET.TERM.INFERENCE.LIMIT 10)
(DEFVAR DP*SET.TERM.INFERENCE.LOWER.LIMIT 5)
(DEFVAR DP*SET.TERM.INFERENCE.ACTUAL 0)
(DEFVAR DP*SET.TERM.INFERENCES.CLAUSE.LIMIT 10)
(DEFVAR DP*SET.MAX.DIFFERENT.TERMS 20)
(DEFVAR DP*SET.MAX.OCCURRENCES 6)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                                                                                                                      ;;;
;;;                                         INTERFACE FUNCTION                                                           ;;;
;;;                                                                                                                      ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(DEFUN DP-SET.SIMPLIFICATION (GTERM &optional constant.variables)
  
  ;;; Edited : 26.04.94 by CS
  ;;; Input  : a formula and a list of variables
  ;;; Effect : first the formula is normalized and then given to the set prover in order
  ;;;          to find a refutation, \verb$CONSTANT.VARIABLES$ are treated as constants
  ;;; Value  : in case the formula could be refuted the literal false is returned, otherwise
  ;;;          the original formula

  (let (termsubst)
    (MAPC #'(LAMBDA (VAR)
	      (SETQ TERMSUBST
		    (UNI-TERMSUBST.CREATE
		     TERMSUBST (DA-TERM.CREATE VAR) 
		     (DA-TERM.CREATE (DA-FUNCTION.CREATE NIL (DA-SYMBOL.SORT VAR) NIL T)))))
	  CONSTANT.VARIABLES)
    (SETQ GTERM (UNI-TERMSUBST.APPLY TERMSUBST GTERM))  
    (LET* ((VARIABLES (DA-GTERM.VARIABLES GTERM))
	   (SET.SORTS (DELETE-DUPLICATES (DP=SET.GET.SET.SORTS GTERM) :TEST #'EQ))
	   (ACTUAL.GTERM (DP=SET.NORMALIZE.GTERM.PREDICATE GTERM VARIABLES SET.SORTS))
	   clauses TERMLIST COUNTER MAX.COUNTER)

	  (cond ((> (dp=set.simplification.clause.count actual.gterm) 50)
		 gterm)
		(t (setq CLAUSES (DELETE-DUPLICATES
				  (MAPCAN #'DP=SET.SIMPLE.INFERENCE
					  (NORM=GET.CLAUSELIST (NORM=TRANSFORM.TO.PSEUDO.CNF ACTUAL.GTERM)))
				  :TEST #'DP=SET.CLAUSE.ARE.EQUAL))
		   (COND ((SOME #'NULL CLAUSES)
			  (DP-LITERAL.FALSE))
			 (T (MULTIPLE-VALUE-SETQ (TERMLIST COUNTER MAX.COUNTER)
						 (DP=SET.YIELD.TERMLIST CLAUSES))
			    (COND ((DP=SET.REDUCE.CLAUSES CLAUSES TERMLIST COUNTER MAX.COUNTER)
				   (DP-LITERAL.FALSE))
				  (T GTERM)))))))))

(defun dp=set.simplification.clause.count (gterm &optional (operator 'and) (symbol '+))

  ;;; Edited : 6.6.97 by CS
  ;;; Input  : a gterm, optionally an operator ('and or 'or) and an arithmetic symbol ('+ or '*)
  ;;; Value  : the number of clauses that would be generated if gterm would be in
  ;;;          clause normal form

  (cond ((da-literal.is gterm) 1)
	(t (cond ((or (eq (da-gterm.symbol gterm) 'all)
		      (eq (da-gterm.symbol gterm) 'ex))
		  (dp=set.simplification.clause.count (second (da-gterm.termlist gterm)) operator symbol))
		 ((eq (da-gterm.symbol gterm)
		      operator)
		  (eval (cons symbol (mapcar #'(lambda (sub.gterm)
						 (dp=set.simplification.clause.count 
						  sub.gterm 
						  (cond ((eq operator 'and) 'or)
							((eq operator 'or) 'and)
							(t operator))
						  (cond ((eq symbol '+) '*)
							((eq symbol '*) '+)
							(t symbol))))
					     (da-gterm.termlist gterm)))))
		 ((or (and (eq operator 'and)
			   (eq (da-gterm.symbol gterm)  'or))
		      (and (eq operator 'or)
			   (eq (da-gterm.symbol gterm) 'and)))
		  (eval (cons (cond ((eq symbol '+) '*)
				    (t '+))
			      (mapcar #'(lambda (sub.gterm)
					  (dp=set.simplification.clause.count sub.gterm
							     operator symbol))
				      (da-gterm.termlist gterm)))))
		 (t 10000)))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                                                                                                                      ;;;
;;;                                             HEURISTICS                                                               ;;;
;;;                                                                                                                      ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(DEFUN DP=SET.REDUCE.CLAUSES (CLAUSES TERMLIST COUNTER MAX.COUNTER)
  
  ;;; Edited : 24.02.94 by CS
  ;;; Input  : a set of clauses, a termlist which contains all those terms which can still be checked for
  ;;;          chaining, and a counter needed for aborting the prover
  ;;; Effect : if there is no empty clause in CLAUSES then CLAUSES are refuted by
  ;;;          making inferences about subterms of literals in CLAUSES
  
  (LET (TERM CLAUSE NEW.CLAUSES RESULT TAG LOCAL.TERMLIST LOCAL.COUNTER LOCAL.MAX.COUNTER)
    (COND ((> DP*SET.REDUCE.ACTUAL DP*SET.REDUCE.LIMIT) NIL)
	  ((OR (> COUNTER DP*SET.MAX.DIFFERENT.TERMS)
	       (> MAX.COUNTER DP*SET.MAX.OCCURRENCES))
	   NIL)
	  (TERMLIST
	   (SETQ TERM (CAR (FIRST TERMLIST)))
	   (SETQ CLAUSE (CDR (FIRST TERMLIST)))
	   (COND ((DA-VARIABLE.IS (DA-TERM.SYMBOL TERM))
		  (COND ((NULL (SETQ NEW.CLAUSES (DP=SET.VARIABLE.INFERENCE
						  (DA-TERM.SYMBOL TERM)
						  CLAUSE (REMOVE CLAUSE CLAUSES :TEST #'DP=SET.CLAUSE.ARE.EQUAL))))
			 (DP=SET.REDUCE.CLAUSES CLAUSES (REST TERMLIST) COUNTER MAX.COUNTER))
			((SOME #'NULL NEW.CLAUSES) T) ;;; JETZT EVTL. NOCH GLEICH CHECKEN OB ERFOLG, SIEHE UNTEN,
			                              ;;; WENN NICHT, DANN NOCHMAL DAS GANZE MIT CONS TERM TERMLIST
			((NULL (SET-DIFFERENCE NEW.CLAUSES CLAUSES :TEST #'DP=SET.CLAUSE.ARE.EQUAL))
			 (DP=SET.REDUCE.CLAUSES CLAUSES (REST TERMLIST) COUNTER MAX.COUNTER))
			(T (SETQ NEW.CLAUSES (UNION CLAUSES NEW.CLAUSES :TEST #'DP=SET.CLAUSE.ARE.EQUAL))
			   (UNWIND-PROTECT
			       (PROGN (INCF DP*SET.REDUCE.ACTUAL)
				      (MULTIPLE-VALUE-SETQ (LOCAL.TERMLIST LOCAL.COUNTER LOCAL.MAX.COUNTER)
					(DP=SET.YIELD.TERMLIST NEW.CLAUSES))
				      (SETQ RESULT (DP=SET.REDUCE.CLAUSES NEW.CLAUSES LOCAL.TERMLIST LOCAL.COUNTER LOCAL.MAX.COUNTER))
				      (SETQ TAG T))
			     (COND (TAG (DECF DP*SET.REDUCE.ACTUAL)
					(SETQ TAG NIL))
				   (T (SETQ DP*SET.REDUCE.ACTUAL 0))))
			   RESULT)))
		 ((NULL (SETQ NEW.CLAUSES (DP=SET.TERM.INFERENCE.CLAUSES TERM CLAUSES)))
		  (DP=SET.REDUCE.CLAUSES CLAUSES (REST TERMLIST) COUNTER MAX.COUNTER))
		 ((SOME #'NULL NEW.CLAUSES) T)
		 ((NULL (SET-DIFFERENCE NEW.CLAUSES CLAUSES :TEST #'DP=SET.CLAUSE.ARE.EQUAL))
		  (DP=SET.REDUCE.CLAUSES CLAUSES (REST TERMLIST) COUNTER MAX.COUNTER))
		 (T (UNWIND-PROTECT
			(PROGN (INCF DP*SET.REDUCE.ACTUAL)
			       (MULTIPLE-VALUE-SETQ (LOCAL.TERMLIST LOCAL.COUNTER LOCAL.MAX.COUNTER)
				 (DP=SET.YIELD.TERMLIST NEW.CLAUSES))
			       (SETQ RESULT (DP=SET.REDUCE.CLAUSES NEW.CLAUSES LOCAL.TERMLIST LOCAL.COUNTER LOCAL.MAX.COUNTER))
			       (SETQ TAG T))
		      (COND (TAG (DECF DP*SET.REDUCE.ACTUAL)
				 (SETQ TAG NIL))
			    (T (SETQ DP*SET.REDUCE.ACTUAL 0))))
		    (COND (RESULT)
			  (T (SETQ CLAUSES (UNION CLAUSES NEW.CLAUSES :TEST #'DP=SET.CLAUSE.ARE.EQUAL))
			     (UNWIND-PROTECT
				 (PROGN (INCF DP*SET.REDUCE.ACTUAL)
					(MULTIPLE-VALUE-SETQ (LOCAL.TERMLIST LOCAL.COUNTER LOCAL.MAX.COUNTER)
					  (DP=SET.YIELD.TERMLIST CLAUSES))
					(SETQ RESULT (DP=SET.REDUCE.CLAUSES CLAUSES LOCAL.TERMLIST LOCAL.COUNTER LOCAL.MAX.COUNTER))
					(SETQ TAG T))
			       (COND (TAG (DECF DP*SET.REDUCE.ACTUAL)
					  (SETQ TAG NIL))
				     (T (SETQ DP*SET.REDUCE.ACTUAL 0))))
			     RESULT)))))
	  (T NIL))))


(DEFUN DP=SET.SIMPLE.INFERENCE (CLAUSE)
  
  ;;; Edited : 21.02.94 by CS
  ;;; Input  : a clause
  ;;; Value  : a list of clauses, drawn by simple inference steps:
  ;;;          1. splitting and flattening
  ;;;          2. factoring
  ;;;          3. singleton reduction
  ;;;          4. trivial reductions

  (MAPCAR #'DP=SET.SINGLETON.REDUCTION
	  (MAPCAN #'(LAMBDA (CL)
		      (COND ((DP=SET.FACTORING CL))
			    (T (LIST CL))))
		  (DP=SET.TRIVIAL.REDUCTION (DP=SET.SPLIT.AND.FLATTEN.CLAUSE CLAUSE)))))



(DEFUN DP=SET.VARIABLE.INFERENCE (VARIABLE CLAUSE CLAUSES)
  
  ;;; Edited : 24.02.94 by CS
  ;;; Input  : a variable, a clause, and a set of clauses
  ;;; Effect : all variable inferences of clause are drawn (with clauses)
  ;;; Value  : a new set of clauses

  (DELETE-DUPLICATES
   (MAPCAN #'DP=SET.SIMPLE.INFERENCE
	   (APPEND (DP=SET.VARIABLE.ELIMINATION CLAUSE VARIABLE)
		   (DP=SET.FACTORING.ON.VARIABLE VARIABLE CLAUSE)
		   (MAPCAN #'(LAMBDA (CL)
			       (APPEND (DP=SET.LVT.CHAIN.RESOLVENT CLAUSE CL VARIABLE)
				       (DP=SET.LV.CHAIN.RESOLVENT CLAUSE CL VARIABLE)
				       (DP=SET.RVT.CHAIN.RESOLVENT CLAUSE CL VARIABLE)))
			   CLAUSES)))
   :TEST #'DP=SET.CLAUSE.ARE.EQUAL))



(DEFUN DP=SET.TERM.INFERENCE.CLAUSE (TERM CLAUSE CLAUSES)
  
  ;;; Edited : 24.02.94 by CS
  ;;; Input  : a term (no variable), a clause, and a set of clauses
  ;;; Effect : all inferences of clause are draw (wrt. TERM)
  ;;; Value  : a new set of clauses

  (DELETE-DUPLICATES
   (MAPCAN #'DP=SET.SIMPLE.INFERENCE
	   (MAPCAN #'(LAMBDA (CL)
		       (DP=SET.BASIC.SUBSET.CHAINING CLAUSE CL TERM))
		   CLAUSES))
   :TEST #'DP=SET.CLAUSE.ARE.EQUAL))


(DEFUN DP=SET.TERM.INFERENCE.CLAUSES (TERM CLAUSES &OPTIONAL ALREADY)
  
  ;;; Edited : 24.02.94 by CS
  ;;; Input  : a term and a set of clauses, optional argument used for computing the result
  ;;; Effect : all inferences between clauses are drawn
  ;;; Value  : a set of clauses where each toplevel term does not match with TERM

  (LET (TAG)
    (COND ((> DP*SET.TERM.INFERENCE.ACTUAL DP*SET.TERM.INFERENCE.LIMIT) NIL)
	  ((AND (> DP*SET.TERM.INFERENCE.ACTUAL DP*SET.TERM.INFERENCE.LOWER.LIMIT)
		(> (LIST-LENGTH CLAUSES) DP*SET.TERM.INFERENCES.CLAUSE.LIMIT)) NIL)
	  ((NULL CLAUSES) NIL)
	  (T (LET (NEW.CLAUSES RESULT
			       (CLAUSE (FIRST CLAUSES))
			       (REST.CLAUSES (REST CLAUSES)))
	       (COND ((NOT (DP=SET.TERM.OCCURS.IN.CLAUSE TERM CLAUSE))
		      (UNWIND-PROTECT
			  (PROGN (INCF DP*SET.TERM.INFERENCE.ACTUAL)
				 (SETQ RESULT (ADJOIN CLAUSE (DP=SET.TERM.INFERENCE.CLAUSES TERM REST.CLAUSES ALREADY)
						      :TEST #'DP=SET.CLAUSE.ARE.EQUAL))
				 (SETQ TAG T))
			(COND (TAG (DECF DP*SET.TERM.INFERENCE.ACTUAL)
				   (SETQ TAG NIL))
			      (T (SETQ DP*SET.TERM.INFERENCE.ACTUAL 0))))
		      RESULT)
		     (T (UNWIND-PROTECT
			    (PROGN (INCF DP*SET.TERM.INFERENCE.ACTUAL)
				   (SETQ NEW.CLAUSES (DP=SET.TERM.INFERENCE.CLAUSE TERM CLAUSE REST.CLAUSES))
				   (SETQ ALREADY (ADJOIN CLAUSE ALREADY :TEST #'DP=SET.CLAUSE.ARE.EQUAL))
				   (SETQ NEW.CLAUSES (SET-DIFFERENCE (UNION NEW.CLAUSES REST.CLAUSES :TEST #'DP=SET.CLAUSE.ARE.EQUAL)
								     ALREADY
								     :TEST #'DP=SET.CLAUSE.ARE.EQUAL))
				   (SETQ RESULT
					 (DP=SET.TERM.INFERENCE.CLAUSES TERM NEW.CLAUSES ALREADY))
				   (SETQ TAG T))
			  (COND (TAG (DECF DP*SET.TERM.INFERENCE.ACTUAL)
				     (SETQ TAG NIL))
				(T (SETQ DP*SET.TERM.INFERENCE.ACTUAL 0))))
			RESULT)))))))






(DEFUN DP=SET.TERM.OCCURS.IN.CLAUSE (TERM CLAUSE)
  
  ;;; Edited : 24.02.94 by CS
  ;;; Input  : a term and a clause
  ;;; Value  : T, iff there is a toplevel term in a literal of CLAUSE which unifies with TERM

  (SOME #'(LAMBDA (LITERAL)
	    (SOME #'(LAMBDA (SUBTERM)
		      (UNI-TERM.UNIFY SUBTERM TERM))
		  (APPEND (DP=SET.LITERAL.LEFT.TERMLIST LITERAL)
			  (DP=SET.LITERAL.RIGHT.TERMLIST LITERAL))))
	(REMOVE-IF-NOT #'DP=SET.LITERAL.IS CLAUSE)))


(DEFUN DP=SET.YIELD.TERMLIST (CLAUSES)
  
  ;;; Edited : 24.02.94 by CS
  ;;; Input  : a set of clauses
  ;;; Values : 1. a list of dotted pairs consisting of a toplevel term of a predefined set literal in CLAUSES and 
  ;;;             the corresponding clause
  ;;;          2. the length of the resulting termlist (of dotted pairs) (used for abortion criterion)
  ;;;          3. the maximal number of occurrences of a toplevel term in clauses (used for abortion criterion)

  (LET (VARIABLES TERMS.RIGHT TERMS.LEFT LEFT.SINGLETONS RIGHT.SINGLETONS TERMLIST.RESULT
		  COUNTER MAX.COUNTER DUMMY)
    (MAPC #'(LAMBDA (CLAUSE)
	      (MAPC #'(LAMBDA (LITERAL)
			(LET ((LEFT (DP=SET.LITERAL.LEFT.TERMLIST LITERAL))
			      (RIGHT (DP=SET.LITERAL.RIGHT.TERMLIST LITERAL)))
			  (MAPC #'(LAMBDA (LEFT.TERM)
				    (COND ((DA-VARIABLE.IS (DA-TERM.SYMBOL LEFT.TERM))
					   (SETQ VARIABLES (CONS (CONS LEFT.TERM CLAUSE) VARIABLES)))
					  ((EQ (DA-TERM.SYMBOL LEFT.TERM) (DP-FUNCTION.SET.INSERT (DA-TERM.SORT LEFT.TERM)))
					   (SETQ LEFT.SINGLETONS (CONS (CONS LEFT.TERM CLAUSE) LEFT.SINGLETONS)))
					  (T (SETQ TERMS.LEFT (CONS (CONS LEFT.TERM CLAUSE) TERMS.LEFT)))))
				LEFT)
			  (MAPC #'(LAMBDA (RIGHT.TERM)
				    (COND ((DA-VARIABLE.IS (DA-TERM.SYMBOL RIGHT.TERM))
					   (SETQ VARIABLES (CONS (CONS RIGHT.TERM CLAUSE) VARIABLES)))
					  ((EQ (DA-TERM.SYMBOL RIGHT.TERM) (DP-FUNCTION.SET.INSERT (DA-TERM.SORT RIGHT.TERM)))
					   (SETQ RIGHT.SINGLETONS (CONS (CONS RIGHT.TERM CLAUSE) RIGHT.SINGLETONS)))
					  (T (SETQ TERMS.RIGHT (CONS (CONS RIGHT.TERM CLAUSE) TERMS.RIGHT)))))
				RIGHT)))
		    (REMOVE-IF-NOT #'DP=SET.LITERAL.IS CLAUSE)))
	  (reverse CLAUSES))
    (SETQ DUMMY (APPEND TERMS.RIGHT TERMS.LEFT RIGHT.SINGLETONS VARIABLES LEFT.SINGLETONS))
    (SETQ TERMLIST.RESULT
	  (REMOVE-DUPLICATES DUMMY :TEST #'(LAMBDA (OBJ1 OBJ2)
					     (UNI-TERM.ARE.EQUAL (FIRST OBJ1) (FIRST OBJ2)))))
    (SETQ COUNTER (LENGTH TERMLIST.RESULT))
    (SETQ MAX.COUNTER
	  (COND (TERMLIST.RESULT
		 (APPLY #'MAX (MAPCAR #'(LAMBDA (OBJECT)
					  (COUNT OBJECT DUMMY :TEST #'(LAMBDA (OBJ1 OBJ2)
									(UNI-TERM.ARE.EQUAL (FIRST OBJ1) (FIRST OBJ2)))))
				      TERMLIST.RESULT)))
		(T 0)))
    (VALUES TERMLIST.RESULT COUNTER MAX.COUNTER)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                                                                                                                      ;;;
;;;                                             NORMALIZATION                                                            ;;;
;;;                                                                                                                      ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(DEFUN DP=SET.GET.SET.SORTS (GTERM)
  
  ;;; Edited : 01.03.94 by CS
  ;;; Input  : a gterm
  ;;; Value  : a list of set sorts occuring in gterm

  (COND ((DA-LITERAL.IS GTERM)
	 (COND ((DP=SET.LITERAL.IS GTERM)
		(COND ((EQ (DA-LITERAL.SYMBOL GTERM) (DP-PREDICATE.SET.DELTA.SUBSET (DA-TERM.SORT (FIRST (DA-LITERAL.TERMLIST GTERM)))))
		       (LIST (DA-TERM.SORT (FIRST (DA-LITERAL.TERMLIST GTERM)))))
		      (T (LIST (DA-TERM.SORT (SECOND (DA-LITERAL.TERMLIST GTERM)))))))
	       (T NIL)))
	(T (MAPCAN #'DP=SET.GET.SET.SORTS (DA-GTERM.TERMLIST GTERM)))))

(DEFUN DP=SET.NORMALIZE.GTERM.PREDICATE (GTERM VARIABLES SET.SORTS)
  
  ;;; Edited : 26.04.94 by CS
  ;;; Input  : a formula, a list of variables, part of them occurring in the formula,
  ;;;          and a list of set sorts part of them occuring in the formula
  ;;; Value  : formula is converted into the normal form for the set prover

  (LET (NEW.GTERM)
    (COND ((DA-LITERAL.IS GTERM)
	   (COND ((DP=SET.LITERAL.IS GTERM)
		  (DP=SET.NORMALIZE.LITERAL.PREDICATE GTERM VARIABLES))
		 ((SETQ NEW.GTERM (DP=SET.LITERAL.IS.NON.SET.EQUALITY GTERM SET.SORTS))
		  (DP=SET.NORMALIZE.GTERM.PREDICATE NEW.GTERM VARIABLES SET.SORTS))
		 (T GTERM)))
	  (T (DP=SET.NORMALIZE.TWO.ARY.GTERM (DA-GTERM.SYMBOL GTERM)
					     (MAPCAR #'(LAMBDA (TERM)
							 (DP=SET.NORMALIZE.GTERM.PREDICATE TERM VARIABLES SET.SORTS))
						     (DA-GTERM.TERMLIST GTERM)))))))


(DEFUN DP=SET.NORMALIZE.TWO.ARY.GTERM (SYMBOL GTERMS)
  
  ;;; Edited : 26.04.94 by CS
  ;;; Input  : a symbol (or, and) and a list of subformulas
  ;;; Value  : calls the normalization for each literal, resulting formula is created
  ;;;          using 2-ary AND and 2-ary OR
  
  (COND ((NULL (CDR GTERMS)) (FIRST GTERMS))
	(T (DA-FORMULA.CREATE SYMBOL (LIST (FIRST GTERMS)
					   (DP=SET.NORMALIZE.TWO.ARY.GTERM SYMBOL (REST GTERMS)))))))


(DEFUN DP=SET.LITERAL.IS.NON.SET.EQUALITY (LITERAL SET.SORTS)
  
  ;;; Edited : 01.03.94 by CS
  ;;; Input  : a literal and a list of set sorts
  ;;; Value  : if it is an equality literal and the sorts of its arguments are
  ;;;          element sorts of a set sort, then the literal t1 = t2 is transformed into
  ;;;          insert(t1 empty) <= insert(t2 empty), else NIL

  (COND ((DA-LITERAL.IS.EQUALITY LITERAL)
	 (LET* ((LEFT (FIRST (DA-LITERAL.TERMLIST LITERAL)))
		(RIGHT (SECOND (DA-LITERAL.TERMLIST LITERAL)))
		(SORT (COND ((DA-SORT.IS.SUBSORT (DA-TERM.SORT LEFT) (DA-TERM.SORT RIGHT))
			     (DA-TERM.SORT RIGHT))
			    (T (DA-TERM.SORT LEFT))))
		RESULT)
	   (SETQ SET.SORTS (REMOVE-IF-NOT #'(LAMBDA (SET.SORT)
					      (EQ SORT (DP-SORT.ELEMENT.TYPE SET.SORT)) (LIST SET.SORT))
					  SET.SORTS))
	   (SETQ RESULT (MAPCAR #'(LAMBDA (SET.SORT)
				    (DA-LITERAL.CREATE (DA-LITERAL.SIGN LITERAL)
						       (DP-PREDICATE.SET.<= SET.SORT)
						       (LIST (DA-TERM.CREATE (DP-FUNCTION.SET.INSERT SET.SORT)
									     (LIST (DA-TERM.COPY LEFT)
										   (DA-TERM.CREATE (DP-FUNCTION.SET.EMPTY SET.SORT))))
							     (DA-TERM.CREATE (DP-FUNCTION.SET.INSERT SET.SORT)
									     (LIST (DA-TERM.COPY RIGHT)
										   (DA-TERM.CREATE (DP-FUNCTION.SET.EMPTY SET.SORT)))))))
				SET.SORTS))
	   (COND ((NULL RESULT) NIL)
		 ((NULL (CDR RESULT)) (FIRST RESULT))
		 (T (DA-FORMULA.CREATE 'AND RESULT)))))))
						      
    
(DEFUN DP=SET.NORMALIZE.LITERAL.PREDICATE (LITERAL VARIABLES)
  
  ;;; Edited : 26.04.94 by CS
  ;;; Input  : a literal and a list of variables
  ;;; Value  : literal is normalized for set prover, normalization by converting each literal
  ;;;          to one using the subset relation
  
  (LET* ((SYMBOL (DA-LITERAL.SYMBOL LITERAL))
	 LEFT RIGHT SORT)
    (COND ((EQL 2 (LENGTH (DA-LITERAL.TERMLIST LITERAL)))
	   (SETQ LEFT (FIRST (DA-LITERAL.TERMLIST LITERAL)))
	   (SETQ RIGHT (SECOND (DA-LITERAL.TERMLIST LITERAL)))
	   (SETQ SORT (DA-TERM.SORT RIGHT)))
	  (T (SETQ LEFT (FIRST (DA-LITERAL.TERMLIST LITERAL)))
	     (SETQ SORT (DA-TERM.SORT LEFT))))
    (DP=SET.NORMALIZE.GTERM.TERM (COND ((DA-SIGN.IS.NEGATIVE (DA-LITERAL.SIGN LITERAL))
					(COND ((EQ SYMBOL (DP-PREDICATE.EQUALITY))
					       (DP=SET.NORMALIZE.NOT.EQUALITY LEFT RIGHT SORT VARIABLES))
					      ((EQ SYMBOL (DP-PREDICATE.SET.ELEM SORT))
					       (DP=SET.NORMALIZE.NOT.ELEM LEFT RIGHT SORT))
					      ((EQ SYMBOL (DP-PREDICATE.SET.<= SORT))
					       (DP=SET.NORMALIZE.NOT.<= LEFT RIGHT SORT VARIABLES))
					      ((EQ SYMBOL (DP-PREDICATE.SET.>= SORT))
					       (DP=SET.NORMALIZE.NOT.>= LEFT RIGHT SORT VARIABLES))
					      ((EQ SYMBOL (DP-PREDICATE.SET.DELTA.SUBSET SORT))
					       (DP=SET.NORMALIZE.EQUALITY LEFT (DA-TERM.CREATE (DP-FUNCTION.SET.EMPTY SORT)) SORT))
					      ((EQ SYMBOL (DP-PREDICATE.SET.DELTA.DELETE SORT))
					       (DP=SET.NORMALIZE.NOT.ELEM LEFT RIGHT SORT))
					      ((EQ SYMBOL (DP-PREDICATE.SET.DELTA.INTERSECTION.1 SORT))
					       (DP=SET.NORMALIZE.EQUALITY (DA-TERM.CREATE (DP-FUNCTION.SET.INTERSECTION SORT)
											  (LIST (DA-TERM.COPY LEFT) RIGHT))
									  LEFT SORT))
					      ((EQ SYMBOL (DP-PREDICATE.SET.DELTA.INTERSECTION.2 SORT))
					       (DP=SET.NORMALIZE.EQUALITY (DA-TERM.CREATE (DP-FUNCTION.SET.INTERSECTION SORT)
											  (LIST LEFT (DA-TERM.COPY RIGHT)))
									  RIGHT SORT))
					      ((EQ SYMBOL (DP-PREDICATE.SET.DELTA.DIFFERENCE SORT))
					       (DP=SET.NORMALIZE.EQUALITY (DA-TERM.CREATE (DP-FUNCTION.SET.DIFFERENCE SORT)
											  (LIST (DA-TERM.COPY LEFT) RIGHT))
									  LEFT SORT))))
				       (T (COND ((EQ SYMBOL (DP-PREDICATE.EQUALITY))
						 (DP=SET.NORMALIZE.EQUALITY LEFT RIGHT SORT))
						((EQ SYMBOL (DP-PREDICATE.SET.ELEM SORT))
						 (DP=SET.NORMALIZE.ELEM LEFT RIGHT SORT))
						((EQ SYMBOL (DP-PREDICATE.SET.>= SORT))
						 (DP=SET.NORMALIZE.>= LEFT RIGHT SORT))
						((EQ SYMBOL (DP-PREDICATE.SET.<= SORT))
						 (DA-LITERAL.COPY LITERAL))
						((EQ SYMBOL (DP-PREDICATE.SET.DELTA.SUBSET SORT))
						 (DP=SET.NORMALIZE.NOT.EQUALITY LEFT (DA-TERM.CREATE (DP-FUNCTION.SET.EMPTY SORT))
										SORT VARIABLES))
						((EQ SYMBOL (DP-PREDICATE.SET.DELTA.DELETE SORT))
						 (DP=SET.NORMALIZE.ELEM LEFT RIGHT SORT))
						((EQ SYMBOL (DP-PREDICATE.SET.DELTA.INTERSECTION.1 SORT))
						 (DP=SET.NORMALIZE.NOT.EQUALITY (DA-TERM.CREATE (DP-FUNCTION.SET.INTERSECTION SORT)
												(LIST (DA-TERM.COPY LEFT) RIGHT))
										LEFT SORT VARIABLES))
						((EQ SYMBOL (DP-PREDICATE.SET.DELTA.INTERSECTION.2 SORT))
						 (DP=SET.NORMALIZE.NOT.EQUALITY (DA-TERM.CREATE (DP-FUNCTION.SET.INTERSECTION SORT)
												(LIST LEFT (DA-TERM.COPY RIGHT)))
										RIGHT SORT VARIABLES))
						((EQ SYMBOL (DP-PREDICATE.SET.DELTA.DIFFERENCE SORT))
						 (DP=SET.NORMALIZE.NOT.EQUALITY (DA-TERM.CREATE (DP-FUNCTION.SET.DIFFERENCE SORT)
												(LIST (DA-TERM.COPY LEFT) RIGHT))
										LEFT SORT VARIABLES)))))
				 SORT)))

(DEFUN DP=SET.NORMALIZE.GTERM.TERM (GTERM SORT)
  
  ;;; Edited : 26.04.94 by CS
  ;;; Input  : a formula and a specific set sort, formula is already normalized with respect to
  ;;;          predicate symbol
  ;;; Value  : normalized formula for set prover, calls normalization for occurring function symbols
  
  (COND ((DA-LITERAL.IS GTERM)
	 (DP=SET.NORMALIZE.LITERAL.TERM GTERM SORT))
	(T (SETF (DA-GTERM.TERMLIST GTERM)
		 (MAPCAR #'(LAMBDA (TERM)
			     (DP=SET.NORMALIZE.GTERM.TERM TERM SORT))
			 (DA-GTERM.TERMLIST GTERM)))
	   GTERM)))


(DEFUN DP=SET.NORMALIZE.LITERAL.TERM (LITERAL SORT)
  
  ;;; Edited : 26.04.94 by CS
  ;;; Input  : a literal and a specific set sort, literal is already normalized with respect to its predicate symbol
  ;;; Value  : literal is normalized on its term level, thus, as left terms only intersections, on the right
  ;;;          only unions
  
  (LET* ((LEFT (FIRST (DA-LITERAL.TERMLIST LITERAL)))
	 (RIGHT (SECOND (DA-LITERAL.TERMLIST LITERAL)))
	 INTERSECTIONS UNIONS TERM)
    (MULTIPLE-VALUE-SETQ (INTERSECTIONS TERM)
      (DP=SET.NORMALIZE.ANALYZE.INTERSECTION.TERM LEFT SORT))
    (COND (TERM
	   (LET ((SYMBOL (DA-TERM.SYMBOL TERM)))
	     (COND ((EQ SYMBOL (DP-FUNCTION.SET.DIFFERENCE SORT))
		    (DP=SET.NORMALIZE.LITERAL.TERM (DP=SET.NORMALIZE.LITERAL.TERM.LEFT.DIFFERENCE
						    INTERSECTIONS TERM RIGHT SORT) SORT))
		   ((EQ SYMBOL (DP-FUNCTION.SET.SYM.DIFFERENCE SORT))
		    (DP=SET.NORMALIZE.LITERAL.TERM (DP=SET.NORMALIZE.LITERAL.TERM.LEFT.SYM.DIFFERENCE
						    INTERSECTIONS TERM RIGHT SORT) SORT))
		   ((EQ SYMBOL (DP-FUNCTION.SET.UNION SORT))
		    (DP=SET.NORMALIZE.GTERM.TERM (DP=SET.NORMALIZE.LITERAL.TERM.LEFT.UNION
						  INTERSECTIONS TERM RIGHT SORT) SORT))
		   ((EQ SYMBOL (DP-FUNCTION.SET.DELETE SORT))
		    (DP=SET.NORMALIZE.LITERAL.TERM (DP=SET.NORMALIZE.LITERAL.TERM.LEFT.DELETE
						    INTERSECTIONS TERM RIGHT SORT) SORT))
		   ((EQ SYMBOL (DP-FUNCTION.SET.INSERT SORT))
		    (DP=SET.NORMALIZE.LITERAL.TERM (DP=SET.NORMALIZE.LITERAL.TERM.LEFT.INSERT
						    INTERSECTIONS TERM RIGHT SORT) SORT))
		   ((EQ SYMBOL (DP-FUNCTION.SET.SUBSET SORT))
		    (DP=SET.NORMALIZE.LITERAL.TERM (DP=SET.NORMALIZE.LITERAL.TERM.LEFT.DIFFERENCE
						    INTERSECTIONS
						    (DA-TERM.CREATE
						     (DP-FUNCTION.SET.DIFFERENCE SORT)
						     (LIST (FIRST (DA-TERM.TERMLIST TERM))
							   (DA-TERM.CREATE (DP-FUNCTION.SET.ELEMENT SORT)
									   (LIST (FIRST (DA-TERM.TERMLIST TERM))))))
						    RIGHT SORT) SORT)))))
	  (T (MULTIPLE-VALUE-SETQ (UNIONS TERM)
	       (DP=SET.NORMALIZE.ANALYZE.UNION.TERM RIGHT SORT))
	     (COND (TERM
		    (LET ((SYMBOL (DA-TERM.SYMBOL TERM)))
		      (COND ((EQ SYMBOL (DP-FUNCTION.SET.DIFFERENCE SORT))
			     (DP=SET.NORMALIZE.GTERM.TERM (DP=SET.NORMALIZE.LITERAL.TERM.RIGHT.DIFFERENCE
							   UNIONS TERM LEFT SORT) SORT))
			    ((EQ SYMBOL (DP-FUNCTION.SET.SYM.DIFFERENCE SORT))
			     (DP=SET.NORMALIZE.LITERAL.TERM (DP=SET.NORMALIZE.LITERAL.TERM.RIGHT.SYM.DIFFERENCE
							     UNIONS TERM LEFT SORT) SORT))
			    ((EQ SYMBOL (DP-FUNCTION.SET.INTERSECTION SORT))
			     (DP=SET.NORMALIZE.GTERM.TERM (DP=SET.NORMALIZE.LITERAL.TERM.RIGHT.INTERSECTION
							   UNIONS TERM LEFT SORT) SORT))
			    ((EQ SYMBOL (DP-FUNCTION.SET.DELETE SORT))
			     (DP=SET.NORMALIZE.LITERAL.TERM (DP=SET.NORMALIZE.LITERAL.TERM.RIGHT.DELETE
							     UNIONS TERM LEFT SORT) SORT))
			    ((EQ SYMBOL (DP-FUNCTION.SET.INSERT SORT))
			     (DP=SET.NORMALIZE.LITERAL.TERM (DP=SET.NORMALIZE.LITERAL.TERM.RIGHT.INSERT
							     UNIONS TERM LEFT SORT) SORT))
			    ((EQ SYMBOL (DP-FUNCTION.SET.SUBSET SORT))
			     (DP=SET.NORMALIZE.LITERAL.TERM (DP=SET.NORMALIZE.LITERAL.TERM.RIGHT.DIFFERENCE
							     UNIONS
							     (DA-TERM.CREATE
							      (DP-FUNCTION.SET.DIFFERENCE SORT)
							      (LIST (FIRST (DA-TERM.TERMLIST TERM))
								    (DA-TERM.CREATE
								     (DP-FUNCTION.SET.ELEMENT SORT)
								     (LIST (FIRST (DA-TERM.TERMLIST TERM))))))
							     LEFT SORT) SORT)))))
		   (T (DP=SET.NORMALIZE.LITERAL.REDUCE INTERSECTIONS UNIONS SORT)))))))


(DEFUN DP=SET.NORMALIZE.LITERAL.REDUCE (INTERSECTIONS UNIONS SORT)
  
  ;;; Edited : 26.04.94 by CS
  ;;; Input  : a list of intersection terms, a list of union terms and a specific set sort
  ;;; Value  : creates a literal with the above specifications, first, however, the
  ;;;          different sets are reduced and obvious solutions are handled specifically
  
  (SETQ INTERSECTIONS  (DELETE-DUPLICATES (DP=SET.NORMALIZE.TERMS (DP-FUNCTION.SET.INTERSECTION SORT) INTERSECTIONS)
					  :TEST #'UNI-TERM.ARE.EQUAL))
  (SETQ UNIONS (DELETE-DUPLICATES (DP=SET.NORMALIZE.TERMS (DP-FUNCTION.SET.UNION SORT) UNIONS)
				  :TEST #'UNI-TERM.ARE.EQUAL))
  (COND ((FIND-IF #'(LAMBDA (SUBTERM)
		      (EQ (DA-TERM.SYMBOL SUBTERM) (DP-FUNCTION.SET.EMPTY SORT)))
		  INTERSECTIONS)
	 (DA-LITERAL.TRUE))
	((INTERSECTION INTERSECTIONS UNIONS :TEST #'UNI-TERM.ARE.EQUAL)
	 (DA-LITERAL.TRUE))
	(T (DP=SET.CREATE.LITERAL INTERSECTIONS
				  (REMOVE-IF #'(LAMBDA (TERM)
						 (EQ (DA-TERM.SYMBOL TERM) (DP-FUNCTION.SET.EMPTY SORT)))
					     UNIONS)
				  SORT))))


(DEFUN DP=SET.NORMALIZE.TERMS (SYMBOL TERMS)
  
  ;;; Edited : 26.04.94 by CS
  ;;; Input  : a function symbol and a list of terms
  ;;; Value  : a list of terms/subterms of TERMS, simplified by AC
  
  (COND ((NULL TERMS) TERMS)
	((EQ SYMBOL (DA-TERM.SYMBOL (FIRST TERMS)))
	 (DP=SET.NORMALIZE.TERMS SYMBOL (APPEND (DA-TERM.TERMLIST (FIRST TERMS)) (REST TERMS))))
	(T (CONS (FIRST TERMS) (DP=SET.NORMALIZE.TERMS SYMBOL (REST TERMS))))))

			      
(DEFUN DP=SET.NORMALIZE.ANALYZE.INTERSECTION.TERM (TERM SORT)
  
  ;;; Edited : 20.01.94 by CS
  ;;; Input  : a term and its sort
  ;;; Effect : separates the term in intersections
  ;;; Values : 1. the intersection of TERM
  ;;;          2. a term (intersected with the intersection) which is not normalized or
  ;;;             NIL if all terms are already normalized

  (LET ((SYMBOL (DA-TERM.SYMBOL TERM))
	NOT.NORMALIZED.TERMS RESULT LOCAL.RESULT LOCAL.NOT.NORMALIZED.TERM)
    (COND ((OR (EQ SYMBOL (DP-FUNCTION.SET.UNION SORT))
	       (EQ SYMBOL (DP-FUNCTION.SET.DIFFERENCE SORT))
	       (EQ SYMBOL (DP-FUNCTION.SET.SYM.DIFFERENCE SORT))
	       (EQ SYMBOL (DP-FUNCTION.SET.DELETE SORT))
	       (AND (EQ SYMBOL (DP-FUNCTION.SET.INSERT SORT))
		    (NEQ (DA-TERM.SYMBOL (SECOND (DA-TERM.TERMLIST TERM)))
			 (DP-FUNCTION.SET.EMPTY SORT))))
	   (VALUES NIL TERM))
	  ((NEQ SYMBOL (DP-FUNCTION.SET.INTERSECTION SORT))
	   (VALUES (LIST TERM) NIL))
	  (T (MAPC #'(LAMBDA (SUBTERM)
		       (MULTIPLE-VALUE-SETQ (LOCAL.RESULT LOCAL.NOT.NORMALIZED.TERM)
			 (DP=SET.NORMALIZE.ANALYZE.INTERSECTION.TERM SUBTERM SORT))
		       (SETQ RESULT (UNION RESULT LOCAL.RESULT :TEST #'UNI-TERM.ARE.EQUAL))
		       (COND (LOCAL.NOT.NORMALIZED.TERM
			      (SETQ NOT.NORMALIZED.TERMS (ADJOIN LOCAL.NOT.NORMALIZED.TERM NOT.NORMALIZED.TERMS
								 :TEST #'UNI-TERM.ARE.EQUAL)))))
		   (DA-TERM.TERMLIST TERM))
	     (COND (NOT.NORMALIZED.TERMS (VALUES (APPEND (REST NOT.NORMALIZED.TERMS) RESULT) (FIRST NOT.NORMALIZED.TERMS)))
		   (T (VALUES RESULT NIL)))))))


(DEFUN DP=SET.NORMALIZE.ANALYZE.UNION.TERM (TERM SORT)
  
  ;;; Edited : 20.01.94 by CS
  ;;; Input  : a term and its sort
  ;;; Effect : separates the term in unions
  ;;; Values : 1. the union of TERM
  ;;;          2. a term (unioned with the union) which is not normalized or
  ;;;             NIL if all terms are already normalized

  (LET ((SYMBOL (DA-TERM.SYMBOL TERM))
	NOT.NORMALIZED.TERMS RESULT LOCAL.RESULT LOCAL.NOT.NORMALIZED.TERM)
    (COND ((OR (EQ SYMBOL (DP-FUNCTION.SET.INTERSECTION SORT))
	       (EQ SYMBOL (DP-FUNCTION.SET.DIFFERENCE SORT))
	       (EQ SYMBOL (DP-FUNCTION.SET.SYM.DIFFERENCE SORT))
	       (EQ SYMBOL (DP-FUNCTION.SET.DELETE SORT))
	       (AND (EQ SYMBOL (DP-FUNCTION.SET.INSERT SORT))
		    (NEQ (DA-TERM.SYMBOL (SECOND (DA-TERM.TERMLIST TERM)))
			 (DP-FUNCTION.SET.EMPTY SORT))))
	   (VALUES NIL TERM))
	  ((NEQ SYMBOL (DP-FUNCTION.SET.UNION SORT))
	   (VALUES (LIST TERM) NIL))
	  (T (MAPC #'(LAMBDA (SUBTERM)
		       (MULTIPLE-VALUE-SETQ (LOCAL.RESULT LOCAL.NOT.NORMALIZED.TERM)
			 (DP=SET.NORMALIZE.ANALYZE.UNION.TERM SUBTERM SORT))
		       (SETQ RESULT (UNION RESULT LOCAL.RESULT :TEST #'UNI-TERM.ARE.EQUAL))
		       (COND (LOCAL.NOT.NORMALIZED.TERM
			      (SETQ NOT.NORMALIZED.TERMS (ADJOIN LOCAL.NOT.NORMALIZED.TERM NOT.NORMALIZED.TERMS
								 :TEST #'UNI-TERM.ARE.EQUAL)))))
		   (DA-TERM.TERMLIST TERM))
	     (COND (NOT.NORMALIZED.TERMS (VALUES (APPEND (REST NOT.NORMALIZED.TERMS) RESULT) (FIRST NOT.NORMALIZED.TERMS)))
		   (T (VALUES RESULT NIL)))))))



(DEFUN DP=SET.NORMALIZE.NOT.EQUALITY (LEFT RIGHT SORT VARIABLES)
  
  ;;; Edited : 09.02.94 by CS
  ;;; Input  : two terms, a specific set sort and a list of variables
  ;;;          the input denotes the literal : left /= right
  ;;; Value  : a formula denoting the normalized literal
  ;;; Effect : see details in Hines: The strive based subset prover
  
  (LET* ((SKOLEM.TERM (DA-TERM.CREATE  (DA-FUNCTION.CREATE NIL (DP-SORT.ELEMENT.TYPE SORT)
							   (MAPCAR #'DA-VARIABLE.SORT VARIABLES) T)
				       (MAPCAR #'DA-TERM.CREATE VARIABLES)))
	 (LIT1 (DA-LITERAL.CREATE (DA-SIGN.PLUS) (DP-PREDICATE.SET.<= SORT)
				  (LIST (DA-TERM.CREATE (DP-FUNCTION.SET.INSERT SORT)
							(LIST (DA-TERM.COPY SKOLEM.TERM)
							      (DA-TERM.CREATE (DP-FUNCTION.SET.EMPTY SORT) NIL)))
					(DA-TERM.CREATE (DP-FUNCTION.SET.UNION SORT)
							(LIST (DA-TERM.COPY LEFT) (DA-TERM.COPY RIGHT))))))
	 (LIT2 (DA-LITERAL.CREATE (DA-SIGN.PLUS) (DP-PREDICATE.SET.<= SORT)
				  (LIST (DA-TERM.CREATE (DP-FUNCTION.SET.INTERSECTION SORT)
							(LIST (DA-TERM.CREATE (DP-FUNCTION.SET.INSERT SORT)
									      (LIST SKOLEM.TERM
										    (DA-TERM.CREATE (DP-FUNCTION.SET.EMPTY SORT) NIL)))
							      (DA-TERM.CREATE (DP-FUNCTION.SET.INTERSECTION SORT)
									      (LIST LEFT RIGHT))))
					(DA-TERM.CREATE (DP-FUNCTION.SET.EMPTY SORT) NIL)))))
    (DA-FORMULA.CREATE 'AND (LIST LIT1 LIT2))))
				
						   

(DEFUN DP=SET.NORMALIZE.NOT.ELEM (LEFT RIGHT SORT)
  
  ;;; Edited : 09.02.94 by CS
  ;;; Input  : two terms and a specific set sort 
  ;;;          the input denotes the literal : not elem(left, right)
  ;;; Value  : a formula denoting the normalized literal
  ;;; Effect : see details in Hines: The strive based subset prover
  
  (DA-LITERAL.CREATE (DA-SIGN.PLUS) (DP-PREDICATE.SET.<= SORT)
		     (LIST (DA-TERM.CREATE (DP-FUNCTION.SET.INTERSECTION SORT)
					   (LIST (DA-TERM.CREATE
						  (DP-FUNCTION.SET.INSERT SORT)
						  (LIST LEFT (DA-TERM.CREATE (DP-FUNCTION.SET.EMPTY SORT) NIL)))
						 RIGHT))
			   (DA-TERM.CREATE (DP-FUNCTION.SET.EMPTY SORT) NIL))))
						   

(DEFUN DP=SET.NORMALIZE.NOT.<= (LEFT RIGHT SORT VARIABLES)
  
  ;;; Edited : 09.02.94 by CS
  ;;; Input  : two terms, a specific set sort and a list of variables
  ;;;          the input denotes the literal : not <=(left, right)
  ;;; Value  : a formula denoting the normalized literal
  ;;; Effect : see details in Hines: The strive based subset prover
  
  (LET* ((SKOLEM.TERM (DA-TERM.CREATE  (DA-FUNCTION.CREATE NIL (DP-SORT.ELEMENT.TYPE SORT)
							   (MAPCAR #'DA-VARIABLE.SORT VARIABLES) T)
				       (MAPCAR #'DA-TERM.CREATE VARIABLES)))
	 (LIT1 (DA-LITERAL.CREATE (DA-SIGN.PLUS) (DP-PREDICATE.SET.<= SORT)
				  (LIST (DA-TERM.CREATE (DP-FUNCTION.SET.INSERT SORT)
							(LIST (DA-TERM.COPY SKOLEM.TERM)
							      (DA-TERM.CREATE (DP-FUNCTION.SET.EMPTY SORT) NIL)))
					LEFT)))
	 (LIT2 (DA-LITERAL.CREATE (DA-SIGN.PLUS) (DP-PREDICATE.SET.<= SORT)
				  (LIST (DA-TERM.CREATE (DP-FUNCTION.SET.INTERSECTION SORT)
							(LIST (DA-TERM.CREATE (DP-FUNCTION.SET.INSERT SORT)
									      (LIST SKOLEM.TERM
										    (DA-TERM.CREATE
										     (DP-FUNCTION.SET.EMPTY SORT) NIL)))
							      RIGHT))
					(DA-TERM.CREATE (DP-FUNCTION.SET.EMPTY SORT) NIL)))))
    (DA-FORMULA.CREATE 'AND (LIST LIT1 LIT2))))


(DEFUN DP=SET.NORMALIZE.NOT.>= (LEFT RIGHT SORT VARIABLES)
  
  ;;; Edited : 09.02.94 by CS
  ;;; Input  : two terms, a specific set sort and a list of variables
  ;;;          the input denotes the literal : not >=(left, right)
  ;;; Value  : a formula denoting the normalized literal
  ;;; Effect : see details in Hines: The strive based subset prover
  
  (DP=SET.NORMALIZE.NOT.<= RIGHT LEFT SORT VARIABLES))
						   

(DEFUN DP=SET.NORMALIZE.EQUALITY (LEFT RIGHT SORT)
  
  ;;; Edited : 09.02.94 by CS
  ;;; Input  : two terms and a specific set sort 
  ;;;          the input denotes the literal : left = right
  ;;; Value  : a formula denoting the normalized literal
  ;;; Effect : see details in Hines: The strive based subset prover
  
  (LET ((LIT1 (DA-LITERAL.CREATE (DA-SIGN.PLUS) (DP-PREDICATE.SET.<= SORT)
				 (LIST (DA-TERM.COPY LEFT) (DA-TERM.COPY RIGHT))))
	(LIT2 (DA-LITERAL.CREATE (DA-SIGN.PLUS) (DP-PREDICATE.SET.<= SORT)
				 (LIST RIGHT LEFT))))
    (DA-FORMULA.CREATE 'AND (LIST LIT1 LIT2))))
						   

(DEFUN DP=SET.NORMALIZE.ELEM (LEFT RIGHT SORT)
  
  ;;; Edited : 09.02.94 by CS
  ;;; Input  : two terms and a specific set sort 
  ;;;          the input denotes the literal : elem(left, right)
  ;;; Value  : a formula denoting the normalized literal
  ;;; Effect : see details in Hines: The strive based subset prover
  
  (DA-LITERAL.CREATE (DA-SIGN.PLUS) (DP-PREDICATE.SET.<= SORT)
		     (LIST (DA-TERM.CREATE (DP-FUNCTION.SET.INSERT SORT)
					   (LIST LEFT (DA-TERM.CREATE (DP-FUNCTION.SET.EMPTY SORT) NIL)))
			   RIGHT)))
						   

(DEFUN DP=SET.NORMALIZE.>= (LEFT RIGHT SORT)
  
  ;;; Edited : 09.02.94 by CS
  ;;; Input  : two terms and a specific set sort 
  ;;;          the input denotes the literal : >=(left, right)
  ;;; Value  : a formula denoting the normalized literal
  ;;; Effect : see details in Hines: The strive based subset prover
  
  (DA-LITERAL.CREATE (DA-SIGN.PLUS) (DP-PREDICATE.SET.<= SORT) (LIST RIGHT LEFT)))


(DEFUN DP=SET.NORMALIZE.LITERAL.TERM.LEFT.DIFFERENCE (INTERSECTIONS NOT.NORMALIZED TERM SORT)
  
  ;;; Edited : 09.02.94 by CS
  ;;; Input  : <=(*(intersections, not.normalized), term), sort is a specific set sort
  ;;;          not.normalized is $\tt \setminus$(...)
  ;;; Value  : a formula denoting the normalized literal
  ;;; Effect : see details in Hines: The strive based subset prover
  
  (LET ((LEFT (FIRST (DA-TERM.TERMLIST NOT.NORMALIZED)))
	(RIGHT (SECOND (DA-TERM.TERMLIST NOT.NORMALIZED))))
    (DP=SET.CREATE.LITERAL (CONS LEFT INTERSECTIONS) (LIST TERM RIGHT) SORT)))

						  
(DEFUN DP=SET.NORMALIZE.LITERAL.TERM.LEFT.SYM.DIFFERENCE (INTERSECTIONS NOT.NORMALIZED TERM SORT)
  
  ;;; Edited : 09.02.94 by CS
  ;;; Input  : <=(*(intersections, not.normalized), term), sort is a specific set sort
  ;;;          not.normalized is  -(...)
  ;;; Value  : a formula denoting the normalized literal
  ;;; Effect : see details in Hines: The strive based subset prover
  
  (LET ((LEFT (FIRST (DA-TERM.TERMLIST NOT.NORMALIZED)))
	(RIGHT (SECOND (DA-TERM.TERMLIST NOT.NORMALIZED))))
    (DA-LITERAL.CREATE (DA-SIGN.PLUS) (DP-PREDICATE.SET.<= SORT)
		       (LIST (DA-TERM.CREATE (DP-FUNCTION.SET.INTERSECTION SORT)
					     (CONS (DA-TERM.CREATE (DP-FUNCTION.SET.UNION SORT)
								   (LIST (DA-TERM.CREATE (DP-FUNCTION.SET.DIFFERENCE SORT)
											 (LIST (DA-TERM.COPY LEFT)
											       (DA-TERM.COPY RIGHT)))
									 (DA-TERM.CREATE (DP-FUNCTION.SET.DIFFERENCE SORT)
											 (LIST RIGHT LEFT))))
						   INTERSECTIONS))
			     TERM))))


(DEFUN DP=SET.NORMALIZE.LITERAL.TERM.LEFT.UNION (INTERSECTIONS NOT.NORMALIZED TERM SORT)
  
  ;;; Edited : 09.02.94 by CS
  ;;; Input  : <=(*(intersections, not.normalized), term), sort is a specific set sort
  ;;;          not.normalized is +(...)
  ;;; Value  : a formula denoting the normalized literal
  ;;; Effect : see details in Hines: The strive based subset prover
  
  (LET ((LEFT (FIRST (DA-TERM.TERMLIST NOT.NORMALIZED)))
	(RIGHT (SECOND (DA-TERM.TERMLIST NOT.NORMALIZED))))
    (DA-FORMULA.CREATE 'AND (LIST (DA-LITERAL.CREATE (DA-SIGN.PLUS) (DP-PREDICATE.SET.<= SORT)
						   (LIST (DA-TERM.CREATE (DP-FUNCTION.SET.INTERSECTION SORT)
									 (CONS LEFT (MAPCAR #'DA-TERM.COPY INTERSECTIONS)))
							 (DA-TERM.COPY TERM)))
				  (DA-LITERAL.CREATE (DA-SIGN.PLUS) (DP-PREDICATE.SET.<= SORT)
						     (LIST (DA-TERM.CREATE (DP-FUNCTION.SET.INTERSECTION SORT)
									   (CONS RIGHT INTERSECTIONS))
							   TERM))))))


(DEFUN DP=SET.NORMALIZE.LITERAL.TERM.LEFT.INSERT (INTERSECTIONS NOT.NORMALIZED TERM SORT)
  
  ;;; Edited : 09.02.94 by CS
  ;;; Input  : <=(*(intersections, not.normalized), term), sort is a specific set sort
  ;;;          not.normalized is insert(...)
  ;;; Value  : a formula denoting the normalized literal
  ;;; Effect : see details in Hines: The strive based subset prover
  
  (LET ((LEFT (FIRST (DA-TERM.TERMLIST NOT.NORMALIZED)))
	(RIGHT (SECOND (DA-TERM.TERMLIST NOT.NORMALIZED))))
    (DA-LITERAL.CREATE (DA-SIGN.PLUS) (DP-PREDICATE.SET.<= SORT)
		       (LIST (DA-TERM.CREATE (DP-FUNCTION.SET.INTERSECTION SORT)
					     (CONS (DA-TERM.CREATE (DP-FUNCTION.SET.UNION SORT)
								   (LIST (DA-TERM.CREATE (DP-FUNCTION.SET.INSERT SORT)
											 (LIST LEFT (DA-TERM.CREATE
												     (DP-FUNCTION.SET.EMPTY SORT)
												     NIL)))
									 RIGHT))
						   INTERSECTIONS))
			     TERM))))


(DEFUN DP=SET.NORMALIZE.LITERAL.TERM.LEFT.DELETE (INTERSECTIONS NOT.NORMALIZED TERM SORT)
  
  ;;; Edited : 09.02.94 by CS
  ;;; Input  : <=(*(intersections, not.normalized), term), sort is a specific set sort
  ;;;          not.normalized is delete(...)
  ;;; Value  : a formula denoting the normalized literal
  ;;; Effect : see details in Hines: The strive based subset prover
  
  (LET ((LEFT (FIRST (DA-TERM.TERMLIST NOT.NORMALIZED)))
	(RIGHT (SECOND (DA-TERM.TERMLIST NOT.NORMALIZED))))
    (DA-LITERAL.CREATE (DA-SIGN.PLUS) (DP-PREDICATE.SET.<= SORT)
		       (LIST (DA-TERM.CREATE (DP-FUNCTION.SET.INTERSECTION SORT)
					     (CONS (DA-TERM.CREATE (DP-FUNCTION.SET.DIFFERENCE SORT)
								   (LIST RIGHT
									 (DA-TERM.CREATE (DP-FUNCTION.SET.INSERT SORT)
											 (LIST LEFT (DA-TERM.CREATE
												     (DP-FUNCTION.SET.EMPTY SORT)
												     NIL)))))
						   INTERSECTIONS))
			     TERM))))


(DEFUN DP=SET.NORMALIZE.LITERAL.TERM.RIGHT.DIFFERENCE (UNIONS NOT.NORMALIZED TERM SORT)
  
  ;;; Edited : 09.02.94 by CS
  ;;; Input  : <=(term, +(unions, not.normalized)), sort is a specific set sort
  ;;;          not.normalized is $\tt \setminus$(...)
  ;;; Value  : a formula denoting the normalized literal
  ;;; Effect : see details in Hines: The strive based subset prover
  
  (LET ((LEFT (FIRST (DA-TERM.TERMLIST NOT.NORMALIZED)))
	(RIGHT (SECOND (DA-TERM.TERMLIST NOT.NORMALIZED))))
    (DA-FORMULA.CREATE 'AND (LIST (DA-LITERAL.CREATE (DA-SIGN.PLUS) (DP-PREDICATE.SET.<= SORT)
						     (LIST (DA-TERM.COPY TERM) LEFT))
				  (DA-LITERAL.CREATE (DA-SIGN.PLUS) (DP-PREDICATE.SET.<= SORT)
						     (LIST (DA-TERM.CREATE (DP-FUNCTION.SET.INTERSECTION SORT)
									   (LIST TERM RIGHT))
							   (DA-TERM.CREATE (DP-FUNCTION.SET.UNION SORT)
									   UNIONS)))))))


(DEFUN DP=SET.NORMALIZE.LITERAL.TERM.RIGHT.SYM.DIFFERENCE (UNIONS NOT.NORMALIZED TERM SORT)
  
  ;;; Edited : 09.02.94 by CS
  ;;; Input  : <=(term, +(unions, not.normalized)), sort is a specific set sort
  ;;;          not.normalized is -(...)
  ;;; Value  : a formula denoting the normalized literal
  ;;; Effect : see details in Hines: The strive based subset prover
  
  (LET ((LEFT (FIRST (DA-TERM.TERMLIST NOT.NORMALIZED)))
	(RIGHT (SECOND (DA-TERM.TERMLIST NOT.NORMALIZED))))
    (DA-LITERAL.CREATE (DA-SIGN.PLUS) (DP-PREDICATE.SET.<= SORT)
		       (LIST TERM (DA-TERM.CREATE (DP-FUNCTION.SET.UNION SORT)
						  (CONS (DA-TERM.CREATE (DP-FUNCTION.SET.DIFFERENCE SORT)
									(LIST (DA-TERM.COPY LEFT) (DA-TERM.COPY RIGHT)))
							(CONS (DA-TERM.CREATE (DP-FUNCTION.SET.DIFFERENCE SORT)
									      (LIST RIGHT LEFT))
							      UNIONS)))))))


(DEFUN DP=SET.NORMALIZE.LITERAL.TERM.RIGHT.INTERSECTION (UNIONS NOT.NORMALIZED TERM SORT)
  
  ;;; Edited : 09.02.94 by CS
  ;;; Input  : <=(term, (unions, not.normalized)), sort is a specific set sort
  ;;;          not.normalized is *(...)
  ;;; Value  : a formula denoting the normalized literal
  ;;; Effect : see details in Hines: The strive based subset prover
  
  (LET ((LEFT (FIRST (DA-TERM.TERMLIST NOT.NORMALIZED)))
	(RIGHT (SECOND (DA-TERM.TERMLIST NOT.NORMALIZED))))
    (DA-FORMULA.CREATE 'AND (LIST (DA-LITERAL.CREATE (DA-SIGN.PLUS) (DP-PREDICATE.SET.<= SORT)
						     (LIST (DA-TERM.COPY TERM)
							   (DA-TERM.CREATE (DP-FUNCTION.SET.UNION SORT)
									   (CONS LEFT (MAPCAR #'DA-TERM.COPY UNIONS)))))
				  (DA-LITERAL.CREATE (DA-SIGN.PLUS) (DP-PREDICATE.SET.<= SORT)
						     (LIST TERM (DA-TERM.CREATE (DP-FUNCTION.SET.UNION SORT)
										(CONS RIGHT UNIONS))))))))


(DEFUN DP=SET.NORMALIZE.LITERAL.TERM.RIGHT.INSERT (UNIONS NOT.NORMALIZED TERM SORT)
  
  ;;; Edited : 09.02.94 by CS
  ;;; Input  : <=(term, +(unions, not.normalized)), sort is a specific set sort
  ;;;          not.normalized is insert(...)
  ;;; Value  : a formula denoting the normalized literal
  ;;; Effect : see details in Hines: The strive based subset prover
  
  (LET ((LEFT (FIRST (DA-TERM.TERMLIST NOT.NORMALIZED)))
	(RIGHT (SECOND (DA-TERM.TERMLIST NOT.NORMALIZED))))
    (DA-LITERAL.CREATE (DA-SIGN.PLUS) (DP-PREDICATE.SET.<= SORT)
		       (LIST TERM (DA-TERM.CREATE (DP-FUNCTION.SET.UNION SORT)
						  (CONS (DA-TERM.CREATE (DP-FUNCTION.SET.INSERT SORT)
									(LIST LEFT (DA-TERM.CREATE
										    (DP-FUNCTION.SET.EMPTY SORT) NIL)))
							(CONS RIGHT UNIONS)))))))


(DEFUN DP=SET.NORMALIZE.LITERAL.TERM.RIGHT.DELETE (UNIONS NOT.NORMALIZED TERM SORT)
  
  ;;; Edited : 09.02.94 by CS
  ;;; Input  : <=(term, +(unions, not.normalized)), sort is a specific set sort
  ;;;          not.normalized is delete(...)
  ;;; Value  : a formula denoting the normalized literal
  ;;; Effect : see details in Hines: The strive based subset prover
  
  (LET ((LEFT (FIRST (DA-TERM.TERMLIST NOT.NORMALIZED)))
	(RIGHT (SECOND (DA-TERM.TERMLIST NOT.NORMALIZED))))
    (DA-LITERAL.CREATE (DA-SIGN.PLUS) (DP-PREDICATE.SET.<= SORT)
		       (LIST TERM (DA-TERM.CREATE (DP-FUNCTION.SET.UNION SORT)
						  (CONS (DA-TERM.CREATE
							 (DP-FUNCTION.SET.DIFFERENCE SORT)
							 (LIST (DA-TERM.CREATE
								(DP-FUNCTION.SET.INSERT SORT)
								(LIST LEFT (DA-TERM.CREATE (DP-FUNCTION.SET.EMPTY SORT)
											   NIL)))
							       RIGHT))
							UNIONS))))))
									      


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                                                                                                  ;;;
;;;                                        INFERENCE RULES                                           ;;;
;;;                                                                                                  ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;




(DEFUN DP=SET.NEW.CLAUSE (CLAUSE)
  
  ;;; Edited : 09.02.94 by CS
  ;;; Input  : a clause where each literal is normalized due to the needs of the set prover, thus,
  ;;;          of the form $<=(*(...), +(...))$
  ;;; Value  : each variable is renamed and duplicates in $*(...)$ and $+(...)$ are deleted
  
  (LET* ((VARIABLES (REMOVE-DUPLICATES (MAPCAN #'DA-GTERM.VARIABLES CLAUSE) :TEST #'EQ))
	 (SUBSTITUTION (UNI-CREATE.VAR.RENAMING VARIABLES)))
    (DELETE-DUPLICATES 
     (MAPCAR #'(LAMBDA (LITERAL)
		 (SETQ LITERAL (UNI-SUBST.APPLY SUBSTITUTION LITERAL))
		 (COND ((DP=SET.LITERAL.IS LITERAL)
			(SETF (DA-TERM.TERMLIST (FIRST (DA-LITERAL.TERMLIST LITERAL)))
			      (DELETE-DUPLICATES (DP=SET.LITERAL.LEFT.TERMLIST LITERAL)
						 :TEST #'UNI-TERM.ARE.EQUAL))
			(SETF (DA-TERM.TERMLIST (SECOND (DA-LITERAL.TERMLIST LITERAL)))
			      (DELETE (DA-TERM.CREATE (DP-FUNCTION.SET.EMPTY (DA-TERM.SORT (SECOND (DA-LITERAL.TERMLIST LITERAL)))))
				      (DELETE-DUPLICATES (DP=SET.LITERAL.RIGHT.TERMLIST LITERAL)
							 :TEST #'UNI-TERM.ARE.EQUAL)
				      :TEST #'UNI-TERM.ARE.EQUAL))))
		 LITERAL)
	     CLAUSE)
     :TEST #'DP=SET.LITERAL.ARE.EQUAL)))


(DEFUN DP=SET.CREATE.LITERAL (INTERSECTIONS UNIONS SORT)
  
  ;;; Edited : 09.02.94 by CS
  ;;; Input  : a list of intersections, a list of unions, and a specific set sort
  ;;; Value  : a new literal: $<=(*(intersections), +(unions))$
  
  (DA-LITERAL.CREATE (DA-SIGN.PLUS) (DP-PREDICATE.SET.<= SORT)
		     (LIST (DA-TERM.CREATE (DP-FUNCTION.SET.INTERSECTION SORT)
					   INTERSECTIONS)
			   (DA-TERM.CREATE (DP-FUNCTION.SET.UNION SORT)
					   UNIONS))))
    

  

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                                                                                                  ;;;
;;;                                        BASIC SUBSET CHAINING                                     ;;;
;;;                                                                                                  ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(DEFUN DP=SET.BASIC.SUBSET.CHAINING (CLAUSE1 CLAUSE2 TERM)
  
  ;;; Edited : 09.02.94 by CS
  ;;; Input  : two clauses and a term
  ;;; Value  : a list of clauses due to ``chaining on TERM'' which is a term in a literal of CLAUSE1
  ;;; Effect : see details in Hines: The strive based subset prover

  (LET (UNIFICATORS)
    (APPEND (MAPCAN #'(LAMBDA (LITERAL1)
	     (COND ((DP=SET.LITERAL.IS LITERAL1)
		    (MAPCAN #'(LAMBDA (LEFT1)
		     (COND ((UNI-TERM.ARE.EQUAL LEFT1 TERM)
			    (MAPCAN #'(LAMBDA (LITERAL2)
			     (COND ((DP=SET.LITERAL.IS LITERAL2)
				    (MAPCAN #'(LAMBDA (RIGHT2)
				      (COND ((DA-VARIABLE.IS (DA-TERM.SYMBOL RIGHT2)) NIL)
					    ((SETQ UNIFICATORS (UNI-TERM.UNIFY TERM RIGHT2))
					     (LIST (DP=SET.BASIC.SUBSET.CHAINING.COMPUTE.RESULT.LEFT
						    CLAUSE1 LITERAL1 TERM CLAUSE2 LITERAL2 RIGHT2
						    (FIRST UNIFICATORS))))))
					    (DP=SET.LITERAL.RIGHT.TERMLIST LITERAL2)))))
				    CLAUSE2))))
			    (DP=SET.LITERAL.LEFT.TERMLIST LITERAL1)))))
		    CLAUSE1)
	    (MAPCAN #'(LAMBDA (LITERAL1)
	     (COND ((DP=SET.LITERAL.IS LITERAL1)
		    (MAPCAN #'(LAMBDA (RIGHT1)
		     (COND ((UNI-TERM.ARE.EQUAL RIGHT1 TERM)
			    (MAPCAN #'(LAMBDA (LITERAL2)
			     (COND ((DP=SET.LITERAL.IS LITERAL2)
				    (MAPCAN #'(LAMBDA (LEFT2)
				     (COND ((DA-VARIABLE.IS (DA-TERM.SYMBOL LEFT2)) NIL)
					   ((SETQ UNIFICATORS (UNI-TERM.UNIFY TERM LEFT2))
					    (LIST (DP=SET.BASIC.SUBSET.CHAINING.COMPUTE.RESULT.RIGHT
						   CLAUSE1 LITERAL1 TERM CLAUSE2 LITERAL2 LEFT2
						   (FIRST UNIFICATORS))))))
					    (DP=SET.LITERAL.LEFT.TERMLIST LITERAL2)))))
				    CLAUSE2))))
			    (DP=SET.LITERAL.RIGHT.TERMLIST LITERAL1)))))
		    CLAUSE1))))


(DEFUN DP=SET.BASIC.SUBSET.CHAINING.COMPUTE.RESULT.LEFT (CLAUSE1 LITERAL1 TERM1 CLAUSE2 LITERAL2 TERM2 UNIFICATOR)
  
  ;;; Edited : 09.02.04 by CS
  ;;; Input  : two terms which are terms in the respective literals which are members of the respective clauses
  ;;;          and a unificator of the two terms
  ;;; Value  : computes the result of the chaining inference rule which is a new clause
  
  (DP=SET.NEW.CLAUSE
   (MAPCAR #'(LAMBDA (LITERAL)
	       (UNI-SUBST.APPLY UNIFICATOR LITERAL))
	   (CONS (DP=SET.CREATE.LITERAL (APPEND (REMOVE TERM1 (DP=SET.LITERAL.LEFT.TERMLIST LITERAL1)
							:TEST #'UNI-TERM.ARE.EQUAL)
						(DP=SET.LITERAL.LEFT.TERMLIST LITERAL2))
					(APPEND (DP=SET.LITERAL.RIGHT.TERMLIST LITERAL1)
						(REMOVE TERM2 (DP=SET.LITERAL.RIGHT.TERMLIST LITERAL2)
							:TEST #'UNI-TERM.ARE.EQUAL))
					(DA-TERM.SORT TERM1))
		 (APPEND (REMOVE LITERAL1 CLAUSE1 :TEST #'DP=SET.LITERAL.ARE.EQUAL)
			 (REMOVE LITERAL2 CLAUSE2 :TEST #'DP=SET.LITERAL.ARE.EQUAL))))))
		   
									 

(DEFUN DP=SET.BASIC.SUBSET.CHAINING.COMPUTE.RESULT.RIGHT (CLAUSE1 LITERAL1 TERM1 CLAUSE2 LITERAL2 TERM2 UNIFICATOR)
  
  ;;; Edited : 09.02.04 by CS
  ;;; Input  : two terms which are terms in the respective literals which are members of the respective clauses
  ;;;          and a unificator of the two terms
  ;;; Value  : computes the result of the chaining inference rule which is a new clause
  
  (DP=SET.NEW.CLAUSE
   (MAPCAR #'(LAMBDA (LITERAL)
	       (UNI-SUBST.APPLY UNIFICATOR LITERAL))
	   (CONS (DP=SET.CREATE.LITERAL (APPEND (DP=SET.LITERAL.LEFT.TERMLIST LITERAL1)
						(REMOVE TERM2 (DP=SET.LITERAL.LEFT.TERMLIST LITERAL2)
							:TEST #'UNI-TERM.ARE.EQUAL))
					(APPEND (REMOVE TERM1 (DP=SET.LITERAL.RIGHT.TERMLIST LITERAL1)
							:TEST #'UNI-TERM.ARE.EQUAL)
						(DP=SET.LITERAL.RIGHT.TERMLIST LITERAL2))
					(DA-TERM.SORT TERM1))
		 (APPEND (REMOVE LITERAL1 CLAUSE1 :TEST #'DP=SET.LITERAL.ARE.EQUAL)
			 (REMOVE LITERAL2 CLAUSE2 :TEST #'DP=SET.LITERAL.ARE.EQUAL))))))
		   
  
	
    
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                                                                                                  ;;;
;;;                               SINGLETON REDUCTION  + SIMPLE STUFF                                ;;;
;;;                                                                                                  ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(DEFUN DP=SET.SINGLETON.REDUCTION (CLAUSE)
  
  ;;; Edited : 09.02.94 by CS
  ;;; Input  : a clause
  ;;; Value  : applies singleton reduction rule to clause
  ;;; Effect : see details in Hines: The strive based subset prover

  (LET (TERMSUBST)
    (SETQ CLAUSE (MAPCAN #'(LAMBDA (LITERAL)
			     (COND ((DP=SET.LITERAL.IS LITERAL)
				    (LET ((LEFT (DP=SET.LITERAL.LEFT.TERMLIST LITERAL))
					  (RIGHT (DP=SET.LITERAL.RIGHT.TERMLIST LITERAL)))
				      (COND ((AND (EQL (LENGTH LEFT) 1)
						  (EQ (DA-TERM.SYMBOL (FIRST LEFT)) (DP-FUNCTION.SET.INSERT (DA-TERM.SORT (FIRST LEFT))))
						  (EVERY #'(LAMBDA (SUBTERM)
							     (OR (DA-VARIABLE.IS (DA-TERM.SYMBOL SUBTERM))
								 (EQ (DA-TERM.SYMBOL SUBTERM)
								     (DP-FUNCTION.SET.EMPTY (DA-TERM.SORT SUBTERM)))))
							 RIGHT))
					     (MAPC #'(LAMBDA (VARIABLE)
						       (SETQ TERMSUBST
							     (UNI-TERMSUBST.CREATE
							      TERMSUBST
							      (DA-TERM.CREATE VARIABLE)
							      (DA-TERM.CREATE (DP-FUNCTION.SET.EMPTY (DA-SYMBOL.SORT VARIABLE))))))
						   (DA-GTERM.VARIABLES (SECOND (DA-LITERAL.TERMLIST LITERAL))))
					     NIL)
					    (T (LIST LITERAL)))))
				   (T (LIST LITERAL))))
			 CLAUSE))
    (DP=SET.NEW.CLAUSE
     (MAPCAR #'(LAMBDA (LITERAL)
		 (SETQ LITERAL (UNI-TERMSUBST.APPLY TERMSUBST LITERAL))
		 (COND ((DP=SET.LITERAL.IS LITERAL)
			(SETF (DA-TERM.TERMLIST (FIRST (DA-LITERAL.TERMLIST LITERAL)))
			      (DELETE-DUPLICATES (DP=SET.LITERAL.LEFT.TERMLIST LITERAL)
						 :TEST #'UNI-TERM.ARE.EQUAL))
			(SETF (DA-TERM.TERMLIST (SECOND (DA-LITERAL.TERMLIST LITERAL)))
			      (DELETE-DUPLICATES (DP=SET.LITERAL.RIGHT.TERMLIST LITERAL)
						 :TEST #'UNI-TERM.ARE.EQUAL))))
		 LITERAL)
	     CLAUSE))))



(DEFUN DP=SET.TRIVIAL.REDUCTION (CLAUSE)
  
  ;;; Edited : 21.02.94 by CS
  ;;; Input  : a clause
  ;;; Value  : a list of clauses, the trivial reduction of CLAUSE:
  ;;;          1. if there is a literal in CLAUSE which is true -> NIL
  ;;;          2. if there is a predefined literal with a toplevel subterms of both sides in literal -> NIL
  ;;;          3. if there is a predefined literal with a toplevel subterm of the left side being equal to empty -> NIL
  ;;;          4. else (list CLAUSE)
					    
  (COND ((SOME #'(LAMBDA (LITERAL)
		   (OR (DA-LITERAL.IS.TRUE LITERAL)
		       (AND (DP=SET.LITERAL.IS LITERAL)
			    (OR (FIND-IF #'(LAMBDA (SUBTERM)
					     (EQ (DA-TERM.SYMBOL SUBTERM) (DP-FUNCTION.SET.EMPTY (DA-TERM.SORT SUBTERM))))
					 (DP=SET.LITERAL.LEFT.TERMLIST LITERAL))
				(INTERSECTION (DP=SET.LITERAL.LEFT.TERMLIST LITERAL)
					      (DP=SET.LITERAL.RIGHT.TERMLIST LITERAL)
					      :TEST #'UNI-TERM.ARE.EQUAL)))))
	       CLAUSE)
	 NIL)
	(T (LIST (DELETE-DUPLICATES CLAUSE :TEST #'DP=SET.LITERAL.ARE.EQUAL)))))
	      
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                                                                                                  ;;;
;;;                                        FACTORING                                                 ;;;
;;;                                                                                                  ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(DEFUN DP=SET.FACTORING (LITLIST &OPTIONAL (CLAUSE LITLIST))
  
  ;;; Edited : 09.02.94 by CS
  ;;; Input  : a clause and a litlist (originally clause)
  ;;; Value  : applies the factoring rule to clause, thus, the result are all possible factors of clause
  ;;;          without the original one
  ;;; Effect : see details in Hines: The strive based subset prover

  (DELETE-DUPLICATES (APPEND (DP=SET.FACTORING.LITLIST (FIRST LITLIST) LITLIST CLAUSE)
			     (COND ((REST LITLIST) (DP=SET.FACTORING (REST LITLIST) CLAUSE))))
		     :TEST #'DP=SET.CLAUSE.ARE.EQUAL))
  


(DEFUN DP=SET.FACTORING.LITLIST (LITERAL LITLIST CLAUSE)
  
  ;;; Edited : 09.02.94 by CS
  ;;; Input  : a literal, a litlist, and a clause
  ;;; Value  : applies the factoring rule to clause, thus, the result are all possible factors of clause
  
  (MAPCAN #'(LAMBDA (LIT)
	      (DP=SET.FACTORING.LITERAL LITERAL LIT CLAUSE))
	  LITLIST))


(DEFUN DP=SET.FACTORING.LITERAL (LIT1 LIT2 CLAUSE)
  
  ;;; Edited : 09.02.94 by CS
  ;;; Input  : two literals and a clause
  ;;; Value  : applies the factoring rule to the two literals of clause
  
  (LET (UNIFICATORS NEW.CLAUSE)
    (COND ((AND (DP=SET.LITERAL.IS LIT1)
		(DP=SET.LITERAL.IS LIT2))
	   (APPEND (MAPCAN #'(LAMBDA (TERM1)
			       (MAPCAN #'(LAMBDA (TERM2)
					   (COND ((DA-VARIABLE.IS (DA-TERM.SYMBOL TERM1)) NIL)
						 ((DA-VARIABLE.IS (DA-TERM.SYMBOL TERM2)) NIL)
						 ((UNI-TERM.ARE.EQUAL TERM1 TERM2) NIL)
						 ((SETQ UNIFICATORS (UNI-TERM.UNIFY TERM1 TERM2))
					; ZURUECK: UNIF(CLAUSEL) + FACTORING (UNIF(CLAUSEL))
						  (SETQ NEW.CLAUSE (DP=SET.NEW.CLAUSE
								    (MAPCAR #'(LAMBDA (LITERAL)
										(UNI-SUBST.APPLY (FIRST UNIFICATORS) LITERAL))
									    CLAUSE)))
						  (CONS NEW.CLAUSE (DP=SET.FACTORING NEW.CLAUSE)))))
				       (DP=SET.LITERAL.LEFT.TERMLIST LIT2)))
			   (DP=SET.LITERAL.LEFT.TERMLIST LIT1))
		   (MAPCAN #'(LAMBDA (TERM1)
			       (MAPCAN #'(LAMBDA (TERM2)
					   (COND ((DA-VARIABLE.IS (DA-TERM.SYMBOL TERM1)) NIL)
						 ((DA-VARIABLE.IS (DA-TERM.SYMBOL TERM2)) NIL)
						 ((UNI-TERM.ARE.EQUAL TERM1 TERM2) NIL)
						 ((SETQ UNIFICATORS (UNI-TERM.UNIFY TERM1 TERM2))
					; ZURUECK: UNIF(CLAUSEL) + FACTORING (UNIF(CLAUSEL))
						  (SETQ NEW.CLAUSE (DP=SET.NEW.CLAUSE
								    (MAPCAR #'(LAMBDA (LITERAL)
										(UNI-SUBST.APPLY (FIRST UNIFICATORS) LITERAL))
									    CLAUSE)))
						  (CONS NEW.CLAUSE (DP=SET.FACTORING NEW.CLAUSE)))))
				       (DP=SET.LITERAL.RIGHT.TERMLIST LIT2)))
			   (DP=SET.LITERAL.RIGHT.TERMLIST LIT1)))))))
								   

		       
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                                                                                                  ;;;
;;;                                    FACTORING ON VARIABLES                                        ;;;
;;;                                                                                                  ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(DEFUN DP=SET.VARIABLE.IS.ELIGIBLE.IN.CLAUSE (VARIABLE CLAUSE)
  
  ;;; Edited : 09.02.94 by CS
  ;;; Input  : a variable and a clause
  ;;; Value  : whether the specified variable is eligible for elimination in clause, thus, when
  ;;;          the variable does not occur within any shielding term
  ;;; Effect : see details in Hines: The strive based subset prover
  
  (EVERY #'(LAMBDA (LITERAL)
	     (OR (NOT (DP=SET.LITERAL.IS LITERAL))
		 (EVERY #'(LAMBDA (TAF)
			    (<= (LENGTH TAF) 2))
			(DA-SYMBOL.OCCURS.IN.GTERM VARIABLE LITERAL))))
	 CLAUSE))


(DEFUN DP=SET.FACTORING.ON.VARIABLE (VARIABLE CLAUSE)
  
  ;;; Edited : 09.02.94 by CS
  ;;; Input  : a variable and a clause
  ;;; Value  : applies the rule ``factoring on variables''
  ;;; Effect : see details in Hines: The strive based subset prover
  
  (LET ((VARIABLE.TERM (DA-TERM.CREATE VARIABLE))
	(SORT (DA-SYMBOL.SORT VARIABLE))			
	REST.TERMS)
    (COND ((DP=SET.VARIABLE.IS.ELIGIBLE.IN.CLAUSE VARIABLE CLAUSE)
	   (MAPCAN #'(LAMBDA (LITERAL)
		       (COND ((DP=SET.LITERAL.IS LITERAL)
			      (COND ((AND (FIND-IF #'(LAMBDA (TERM)
						       (EQ (DA-TERM.SYMBOL TERM) VARIABLE))
						   (DP=SET.LITERAL.LEFT.TERMLIST LITERAL))
					  (SETQ REST.TERMS (REMOVE VARIABLE.TERM (DP=SET.LITERAL.LEFT.TERMLIST LITERAL)
								   :TEST #'UNI-TERM.ARE.EQUAL)))
				     (MAPCAN #'(LAMBDA (TERM)
						 (LET ((SUBSTITUTION
							(UNI-TERMSUBST.CREATE NIL VARIABLE.TERM
									      (DA-TERM.CREATE (DP-FUNCTION.SET.UNION SORT)
											      (LIST (DA-TERM.COPY TERM)
												    (DA-TERM.CREATE
												     (DA-VARIABLE.CREATE SORT)))))))
						   (LIST (DP=SET.NEW.CLAUSE
							  (MAPCAR #'(LAMBDA (LIT)
								      (UNI-TERMSUBST.APPLY SUBSTITUTION LIT))
								  (CONS (DP=SET.CREATE.LITERAL REST.TERMS
											       (DA-TERM.TERMLIST
												(SECOND (DA-LITERAL.TERMLIST LITERAL)))
											       SORT)
									(REMOVE LITERAL CLAUSE :TEST #'DP=SET.LITERAL.ARE.EQUAL)))))))
					     REST.TERMS))))))
		   CLAUSE)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                                                                                                  ;;;
;;;                                    SPLITTING AND FLATTENING                                      ;;;
;;;                                                                                                  ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(DEFUN DP=SET.SPLIT.AND.FLATTEN.CLAUSE (CLAUSE)
  
  ;;; Edited : 09.02.94 by CS
  ;;; Input  : a clause
  ;;; Value  : a new clause, splitted and flattened
  ;;; Effect : see details in Hines: The strive based subset prover
  
  (DP=SET.SPLIT.CLAUSE (DP=SET.FLATTEN.CLAUSE CLAUSE)))


(DEFUN DP=SET.SPLIT.CLAUSE (CLAUSE)
  
  ;;; Edited : 09.02.94 by CS
  ;;; Input  : a clause
  ;;; Value  : a new clause, the clause from above without the additional union terms
  ;;; Effect : see details in Hines: The strive based subset prover

  (SETQ CLAUSE (MAPCAR #'(LAMBDA (LITERAL)
			   (COND ((DP=SET.LITERAL.IS LITERAL)
				  (SETF (DA-TERM.TERMLIST (SECOND (DA-LITERAL.TERMLIST LITERAL)))
					(MAPCAN #'(LAMBDA (TERM)
						    (COND ((EQ (DA-TERM.SYMBOL TERM) (DP-FUNCTION.SET.UNION (DA-TERM.SORT TERM)))
							   (DA-TERM.TERMLIST TERM))
							  (T (LIST TERM))))
						(DP=SET.LITERAL.RIGHT.TERMLIST LITERAL)))))
			   LITERAL)
		       CLAUSE))
  (COND ((SOME #'(LAMBDA (LITERAL)
		   (COND ((DP=SET.LITERAL.IS LITERAL)
			  (COND ((SOME #'(LAMBDA (TERM)
					   (COND ((EQ (DA-TERM.SYMBOL TERM) (DP-FUNCTION.SET.UNION (DA-TERM.SORT TERM)))
						  (LET ((REST.TERMS
							 (REMOVE TERM (DP=SET.LITERAL.LEFT.TERMLIST LITERAL)
								 :TEST #'UNI-TERM.ARE.EQUAL))
							(SUBTERMS (DA-TERM.TERMLIST TERM)))
						    (DP=SET.SPLIT.CLAUSE
						     (APPEND (REMOVE LITERAL CLAUSE :TEST #'DP=SET.LITERAL.ARE.EQUAL)
							     (MAPCAR #'(LAMBDA (SUBTERM)
									 (DP=SET.CREATE.LITERAL
									  (CONS SUBTERM REST.TERMS)
									  (DP=SET.LITERAL.RIGHT.TERMLIST LITERAL)
									  (DA-TERM.SORT SUBTERM)))
								     SUBTERMS)))))))
				       (DP=SET.LITERAL.LEFT.TERMLIST LITERAL)))))))
	       CLAUSE))
	(T CLAUSE)))
				   


(DEFUN DP=SET.FLATTEN.CLAUSE (CLAUSE)
  
  ;;; Edited : 09.02.94 by CS
  ;;; Input  : a clause
  ;;; Value  : a new clause, the clause from above without the additional intersection terms
  ;;; Effect : see details in Hines: The strive based subset prover

  (SETQ CLAUSE (MAPCAR #'(LAMBDA (LITERAL)
			   (COND ((DP=SET.LITERAL.IS LITERAL)
				  (SETF (DA-TERM.TERMLIST (FIRST (DA-LITERAL.TERMLIST LITERAL)))
					(MAPCAN #'(LAMBDA (TERM)
						    (COND ((EQ (DA-TERM.SYMBOL TERM) (DP-FUNCTION.SET.INTERSECTION (DA-TERM.SORT TERM)))
							   (DA-TERM.TERMLIST TERM))
							  (T (LIST TERM))))
						(DP=SET.LITERAL.LEFT.TERMLIST LITERAL)))))
			   LITERAL)
		       CLAUSE))
  (COND ((SOME #'(LAMBDA (LITERAL)
		   (COND ((DP=SET.LITERAL.IS LITERAL)
			  (COND ((SOME #'(LAMBDA (TERM)
					   (COND ((EQ (DA-TERM.SYMBOL TERM) (DP-FUNCTION.SET.INTERSECTION (DA-TERM.SORT TERM)))
						  (LET ((REST.TERMS
							 (REMOVE TERM (DP=SET.LITERAL.RIGHT.TERMLIST LITERAL)
								 :TEST #'UNI-TERM.ARE.EQUAL))
							(SUBTERMS (DA-TERM.TERMLIST TERM)))
						    (DP=SET.SPLIT.CLAUSE
						     (APPEND (REMOVE LITERAL CLAUSE :TEST #'DP=SET.LITERAL.ARE.EQUAL)
							     (MAPCAR #'(LAMBDA (SUBTERM)
									 (DP=SET.CREATE.LITERAL
									  (DP=SET.LITERAL.RIGHT.TERMLIST LITERAL)
									  (CONS SUBTERM REST.TERMS)
									  (DA-TERM.SORT SUBTERM)))
								     SUBTERMS)))))))
				       (DP=SET.LITERAL.RIGHT.TERMLIST LITERAL)))))))
			 CLAUSE))
	(T CLAUSE)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                                                                                                  ;;;
;;;                                    CHAINING ON VARIABLES                                         ;;;
;;;                                                                                                  ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



(DEFUN DP=SET.LV.CHAIN.RESOLVENT (CLAUSE2 CLAUSE1 VARIABLE)
  
  ;;; Edited : 16.02.94 by CS
  ;;; Input  : two clauses and a variable
  ;;; Value  : a set of new clauses, the LV chain resolvents
  ;;; Effect : see details in Hines: The strive based subset prover

  (MAPCAN #'(LAMBDA (LITERAL1)
   (COND ((DP=SET.LITERAL.IS LITERAL1)
	  (MAPCAN #'(LAMBDA (LITERAL2)
	   (COND ((AND (DP=SET.LITERAL.IS LITERAL2)
		       (EQ (DA-TERM.SORT (FIRST (DA-LITERAL.TERMLIST LITERAL1)))
			   (DA-TERM.SORT (FIRST (DA-LITERAL.TERMLIST LITERAL2)))))
		  (LET ((LEFTS1 (DP=SET.LITERAL.LEFT.TERMLIST LITERAL1))
			(RIGHTS1 (DP=SET.LITERAL.RIGHT.TERMLIST LITERAL1))
			(LEFTS2 (DP=SET.LITERAL.LEFT.TERMLIST LITERAL2))
			(RIGHTS2 (DP=SET.LITERAL.RIGHT.TERMLIST LITERAL2)))
		    (MAPCAN #'(LAMBDA (RIGHT1)
		     (MAPCAN #'(LAMBDA (LEFT1)
		      (MAPCAN #'(LAMBDA (LEFT2)
		       (MAPCAN #'(LAMBDA (LEFT2B)
				   (LET (UNIFICATORS TERM SUBSTITUTION (SORT (DA-TERM.SORT LEFT1)))
				     (COND ((AND (EQ (DA-TERM.SYMBOL LEFT2B) VARIABLE)
						 (NOT (DA-VARIABLE.IS (DA-TERM.SYMBOL RIGHT1)))
						 (EQ (DP-FUNCTION.SET.INSERT SORT)
						     (DA-TERM.SYMBOL LEFT1))
						 (EQ (DP-FUNCTION.SET.INSERT SORT)
						     (DA-TERM.SYMBOL LEFT2))
						 (DA-GTERM.OCCURS.IN.GTERM LEFT2B LEFT2)
						 (EVERY #'(LAMBDA (TAF)
							    (AND (DA-TAF.IS.LEFT (DA-TAF.TOPLEVEL TAF))
								 (OR (EQ (DA-TERM.SYMBOL
									  (SETQ TERM (DA-ACCESS (DA-TAF.SUPER.TAF TAF (- (LENGTH TAF) 2))
												LITERAL2)))
									 (DP-FUNCTION.SET.INSERT SORT))
								     (DA-VARIABLE.IS (DA-TERM.SYMBOL TERM)))))
							(DA-GTERM.OCCURS.IN.GTERM LEFT2B LITERAL2))
						 (SETQ SUBSTITUTION
						       (UNI-TERMSUBST.CREATE NIL LEFT2B (DA-TERM.CREATE
											 (DP-FUNCTION.SET.UNION SORT)
											 (LIST RIGHT1
											       (DA-TERM.CREATE
												(DA-VARIABLE.CREATE SORT))))))
						 (SETQ UNIFICATORS (UNI-TERM.UNIFY LEFT1 (UNI-TERMSUBST.APPLY SUBSTITUTION LEFT2))))
					    (LIST (DP=SET.NEW.CLAUSE
						   (MAPCAR #'(LAMBDA (LITERAL)
							       (UNI-SUBST.APPLY (FIRST UNIFICATORS) (UNI-TERMSUBST.APPLY SUBSTITUTION
															     LITERAL)))
							   (CONS (DP=SET.CREATE.LITERAL
								  (APPEND LEFTS1 (REMOVE LEFT2B LEFTS2 :TEST #'UNI-TERM.ARE.EQUAL))
								  (APPEND (REMOVE RIGHT1 RIGHTS1 :TEST #'UNI-TERM.ARE.EQUAL) RIGHTS2)
								  SORT)
								 (APPEND (REMOVE LITERAL1 CLAUSE1 :TEST #'DP=SET.LITERAL.ARE.EQUAL)
									 (REMOVE LITERAL2 CLAUSE2 :TEST #'DP=SET.LITERAL.ARE.EQUAL))))))))))
			       LEFTS2))
			      LEFTS2))
			     LEFTS1))
			    RIGHTS1)))))
		  CLAUSE2))))
	  CLAUSE1))

					      
					      
					    



(DEFUN DP=SET.LVT.CHAIN.RESOLVENT (CLAUSE2 CLAUSE1 VARIABLE)
  
  ;;; Edited : 16.02.94 by CS
  ;;; Input  : two clauses and a variable
  ;;; Value  : a set of new clauses, the LVT chain resolvents
  ;;; Effect : see details in Hines: The strive based subset prover

  (MAPCAN #'(LAMBDA (LITERAL1)
   (COND ((DP=SET.LITERAL.IS LITERAL1)
	  (MAPCAN #'(LAMBDA (LITERAL2)
	   (COND ((AND (DP=SET.LITERAL.IS LITERAL2)
		       (EQ (DA-TERM.SORT (FIRST (DA-LITERAL.TERMLIST LITERAL1)))
			   (DA-TERM.SORT (FIRST (DA-LITERAL.TERMLIST LITERAL2)))))
		  (LET ((LEFTS1 (DP=SET.LITERAL.LEFT.TERMLIST LITERAL1))
			(RIGHTS1 (DP=SET.LITERAL.RIGHT.TERMLIST LITERAL1))
			(LEFTS2 (DP=SET.LITERAL.LEFT.TERMLIST LITERAL2))
			(RIGHTS2 (DP=SET.LITERAL.RIGHT.TERMLIST LITERAL2)))
		    (MAPCAN #'(LAMBDA (RIGHT1)
		     (MAPCAN #'(LAMBDA (LEFT2)
		      (MAPCAN #'(LAMBDA (LEFT1)
		       (MAPCAN #'(LAMBDA (LEFT2B)
		        (MAPCAN #'(LAMBDA (LEFT2C)
				    (LET (SIGMA TERM SUBSTITUTION TAU (SORT (DA-TERM.SORT LEFT1)))
				      (COND ((AND (EQ (DA-TERM.SYMBOL LEFT2C) VARIABLE)
						  (NOT (DA-VARIABLE.IS (DA-TERM.SYMBOL RIGHT1)))
						  (NOT (DA-VARIABLE.IS (DA-TERM.SYMBOL LEFT2)))
						  (SETQ SIGMA (UNI-TERM.UNIFY RIGHT1 LEFT2))
						  (EQ (DP-FUNCTION.SET.INSERT SORT) (DA-TERM.SYMBOL LEFT1))
						  (EQ (DP-FUNCTION.SET.INSERT SORT) (DA-TERM.SYMBOL LEFT2B))
						  (EVERY #'(LAMBDA (TAF)
							     (AND (DA-TAF.IS.LEFT (DA-TAF.TOPLEVEL TAF))
								  (OR (EQ (DA-TERM.SYMBOL
									   (SETQ TERM (DA-ACCESS (DA-TAF.SUPER.TAF TAF (- (LENGTH TAF) 2))
												 LITERAL2)))
									  (DP-FUNCTION.SET.INSERT SORT))
								      (DA-VARIABLE.IS (DA-TERM.SYMBOL TERM)))
								  (NOT (UNI-TERM.ARE.EQUAL TERM LEFT2))))
							 (DA-GTERM.OCCURS.IN.GTERM LEFT2C LITERAL2))
						  (DA-GTERM.OCCURS.IN.GTERM LEFT2C LEFT2B)
						  (SETQ SUBSTITUTION
							(UNI-TERMSUBST.CREATE NIL LEFT2C (DA-TERM.CREATE
											  (DP-FUNCTION.SET.UNION SORT)
											  (LIST LEFT2
												(DA-TERM.CREATE
												 (DA-VARIABLE.CREATE SORT))))))
						  (SETQ TAU (UNI-TERM.UNIFY (UNI-SUBST.APPLY (FIRST SIGMA) LEFT1)
									    (UNI-SUBST.APPLY (FIRST SIGMA)
												 (UNI-TERMSUBST.APPLY SUBSTITUTION
														      LEFT2B)))))
					     (LIST (DP=SET.NEW.CLAUSE
						    (MAPCAR #'(LAMBDA (LITERAL)
								(UNI-SUBST.APPLY
								 (FIRST TAU) (UNI-SUBST.APPLY
									      (FIRST SIGMA) (UNI-TERMSUBST.APPLY
											     SUBSTITUTION LITERAL))))
							    (CONS (DP=SET.CREATE.LITERAL
								   (APPEND LEFTS1 (REMOVE LEFT2 (REMOVE LEFT2C LEFTS2 :TEST #'UNI-TERM.ARE.EQUAL)
											  :TEST #'UNI-TERM.ARE.EQUAL))
								   (APPEND (REMOVE RIGHT1 RIGHTS1) RIGHTS2)
								   SORT)
								  (APPEND (REMOVE LITERAL1 CLAUSE1 :TEST #'DP=SET.LITERAL.ARE.EQUAL)
									  (REMOVE LITERAL2 CLAUSE2 :TEST #'DP=SET.LITERAL.ARE.EQUAL))))))))))
				LEFTS2))
			       LEFTS2))
			      LEFTS1))
			     LEFTS2))
			    RIGHTS1)))))
	   CLAUSE2))))
	  CLAUSE1))



(DEFUN DP=SET.RVT.CHAIN.RESOLVENT (CLAUSE1 CLAUSE2 VARIABLE)
  ;;; Edited : 16.02.94 by CS
  ;;; Input  : two clauses and a variable
  ;;; Value  : a set of new clauses, the RVT chain resolvents
  ;;; Effect : see details in Hines: The strive based subset prover

  (MAPCAN #'(LAMBDA (LITERAL1)
   (COND ((DP=SET.LITERAL.IS LITERAL1)
	  (MAPCAN #'(LAMBDA (LITERAL2)
	   (COND ((AND (DP=SET.LITERAL.IS LITERAL2)
		       (EQ (DA-TERM.SORT (FIRST (DA-LITERAL.TERMLIST LITERAL1)))
			   (DA-TERM.SORT (FIRST (DA-LITERAL.TERMLIST LITERAL2)))))
		  (LET ((LEFTS1 (DP=SET.LITERAL.LEFT.TERMLIST LITERAL1))
			(RIGHTS1 (DP=SET.LITERAL.RIGHT.TERMLIST LITERAL1))
			(LEFTS2 (DP=SET.LITERAL.LEFT.TERMLIST LITERAL2))
			(RIGHTS2 (DP=SET.LITERAL.RIGHT.TERMLIST LITERAL2)))
		    (MAPCAN #'(LAMBDA (RIGHT1)
		     (MAPCAN #'(LAMBDA (LEFT2)
		      (MAPCAN #'(LAMBDA (LEFT1)
		       (MAPCAN #'(LAMBDA (LEFT2B)
		        (MAPCAN #'(LAMBDA (RIGHT1B)
				    (LET (SIGMA TERM SUBSTITUTION TAU (SORT (DA-TERM.SORT LEFT1)))
				      (COND ((AND (EQ (DA-TERM.SYMBOL RIGHT1B) VARIABLE)
						  (NOT (DA-VARIABLE.IS (DA-TERM.SYMBOL RIGHT1)))
						  (NOT (DA-VARIABLE.IS (DA-TERM.SYMBOL LEFT2)))
						  (SETQ SIGMA (UNI-TERM.UNIFY RIGHT1 LEFT2))
						  (EQ (DP-FUNCTION.SET.INSERT SORT) (DA-TERM.SYMBOL LEFT1))
						  (EQ (DP-FUNCTION.SET.INSERT SORT) (DA-TERM.SYMBOL LEFT2B))
						  (EVERY #'(LAMBDA (TAF)
							     (OR (AND (DA-TAF.IS.RIGHT (DA-TAF.TOPLEVEL TAF))
								      (DA-VARIABLE.IS (DA-TERM.SYMBOL
										       (DA-ACCESS (DA-TAF.SUPER.TAF
												   TAF (- (LENGTH TAF) 2))
												  LITERAL1))))
								 (AND (DA-TAF.IS.LEFT (DA-TAF.TOPLEVEL TAF))
								      (OR (EQ (DA-TERM.SYMBOL
									       (SETQ TERM (DA-ACCESS (DA-TAF.SUPER.TAF TAF (- (LENGTH TAF) 2))
												     LITERAL1)))
									      (DP-FUNCTION.SET.INSERT SORT))
									  (DA-VARIABLE.IS (DA-TERM.SYMBOL TERM)))
								      (NOT (UNI-TERM.ARE.EQUAL TERM RIGHT1)))))
							 (DA-GTERM.OCCURS.IN.GTERM RIGHT1B LITERAL1))
						  (DA-GTERM.OCCURS.IN.GTERM RIGHT1B LEFT1)
						  (SETQ SUBSTITUTION
							(UNI-TERMSUBST.CREATE NIL RIGHT1B (DA-TERM.CREATE
											   (DP-FUNCTION.SET.INTERSECTION SORT)
											   (LIST RIGHT1
												 (DA-TERM.CREATE
												  (DA-VARIABLE.CREATE SORT))))))
						  (SETQ TAU (UNI-TERM.UNIFY (UNI-SUBST.APPLY (FIRST SIGMA) LEFT2B)
									    (UNI-SUBST.APPLY (FIRST SIGMA)
												 (UNI-TERMSUBST.APPLY SUBSTITUTION
														      LEFT1)))))
					     (LIST (DP=SET.NEW.CLAUSE
						    (MAPCAR #'(LAMBDA (LITERAL)
								(UNI-SUBST.APPLY
								 (FIRST TAU) (UNI-SUBST.APPLY
									      (FIRST SIGMA) (UNI-TERMSUBST.APPLY
											     SUBSTITUTION LITERAL))))
							    (CONS (DP=SET.CREATE.LITERAL
								   (APPEND LEFTS1 (REMOVE LEFT2 LEFTS2 :TEST #'UNI-TERM.ARE.EQUAL))
								   (APPEND (REMOVE RIGHT1 (REMOVE RIGHT1B RIGHTS1 :TEST #'UNI-TERM.ARE.EQUAL)
										   :TEST #'UNI-TERM.ARE.EQUAL)
									   RIGHTS2)
								   SORT)
								  (APPEND (REMOVE LITERAL1 CLAUSE1 :TEST #'DP=SET.LITERAL.ARE.EQUAL)
									  (REMOVE LITERAL2 CLAUSE2 :TEST #'DP=SET.LITERAL.ARE.EQUAL))))))))))
				RIGHTS1))
			       LEFTS2))
			      LEFTS1))
			     LEFTS2))
			    RIGHTS1)))))
		  CLAUSE2))))
	  CLAUSE1))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                                                                                                  ;;;
;;;                                    VARIABLE ELIMINATION                                          ;;;
;;;                                                                                                  ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(DEFUN DP=SET.VARIABLE.ELIMINATION (CLAUSE VARIABLE)
  
  ;;; Edited : 09.02.94 by CS
  ;;; Input  : a clause and a variable, the variable occurring in clause
  ;;; Value  : application of the variable elimination rule, list of clauses
  ;;; Effect : see details in Hines: The strive based subset prover
  
  (LET (VARIABLE.LEFT VARIABLE.RIGHT ELSE)
    (COND ((AND (DA-SORT.IS.INFINITE (DA-SYMBOL.SORT VARIABLE))
		(EVERY #'(LAMBDA (LITERAL)
			   (COND ((DP=SET.LITERAL.IS LITERAL)
				  (COND ((AND (EQL 1 (LENGTH (DP=SET.LITERAL.LEFT.TERMLIST LITERAL)))
					      (EQ (DA-TERM.SYMBOL (FIRST (DP=SET.LITERAL.LEFT.TERMLIST LITERAL)))
						  VARIABLE)
					      (NULL (DA-SYMBOL.OCCURS.IN.GTERM VARIABLE (SECOND (DA-LITERAL.TERMLIST LITERAL)))))
					 (SETQ VARIABLE.LEFT (CONS LITERAL VARIABLE.LEFT)))
					((AND (FIND-IF #'(LAMBDA (TERM)
							   (EQ (DA-TERM.SYMBOL TERM) VARIABLE))
						       (DP=SET.LITERAL.RIGHT.TERMLIST LITERAL))
					      (EVERY #'(LAMBDA (TAF)
							 (AND (DA-TAF.IS.RIGHT (DA-TAF.TOPLEVEL TAF))
							      (EQL 2 (LENGTH TAF))))
						     (DA-SYMBOL.OCCURS.IN.GTERM VARIABLE LITERAL))
					      (NULL (DA-SYMBOL.OCCURS.IN.GTERM VARIABLE (FIRST (DA-LITERAL.TERMLIST LITERAL)))))
					 (SETQ VARIABLE.RIGHT (CONS LITERAL VARIABLE.RIGHT)))
					((NULL (DA-SYMBOL.OCCURS.IN.GTERM VARIABLE LITERAL))
					 (SETQ ELSE (CONS LITERAL ELSE)))))
				 ((NULL (DA-SYMBOL.OCCURS.IN.GTERM VARIABLE LITERAL))
				  (SETQ ELSE (CONS LITERAL ELSE)))))
		       CLAUSE))
	   (LET ((TERM (DA-TERM.CREATE VARIABLE)))
	     (LIST (DP=SET.NEW.CLAUSE
		    (APPEND (MAPCAR #'(LAMBDA (LITERAL)
					(DP=SET.CREATE.LITERAL (DP=SET.LITERAL.LEFT.TERMLIST LITERAL)
							       (REMOVE TERM (DP=SET.LITERAL.RIGHT.TERMLIST LITERAL)
								       :TEST #'UNI-TERM.ARE.EQUAL)
							       (DA-TERM.SORT TERM)))
				    VARIABLE.RIGHT)
			    ELSE))))))))




	   



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                                                                                                                      ;;;
;;;                                            ADDITIONAL STUFF                                                          ;;;
;;;                                                                                                                      ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(DEFUN DP=SET.LITERAL.LEFT.TERMLIST (LITERAL)
  ;;; Edited : 26.04.94 by CS
  ;;; Input  : a literal in normal form
  ;;; Value  : the left intersection termlist of literal
  
  (DA-TERM.TERMLIST (FIRST (DA-LITERAL.TERMLIST LITERAL))))


(DEFUN DP=SET.LITERAL.RIGHT.TERMLIST (LITERAL)
  ;;; Edited : 26.04.94 by CS
  ;;; Input  : a literal in normal form
  ;;; Value  : the right union termlist of literal
  
  (DA-TERM.TERMLIST (SECOND (DA-LITERAL.TERMLIST LITERAL))))


(DEFUN DP=SET.CLAUSE.ARE.EQUAL (CLAUSE1 CLAUSE2)
  ;;; Edited : 26.04.94 by CS
  ;;; Input  : two clauses
  ;;; Value  : T, iff it could be determined that the two clauses are equal
  
  (AND (EVERY #'(LAMBDA (LITERAL1)
		  (FIND LITERAL1 CLAUSE2 :TEST #'DP=SET.LITERAL.ARE.EQUAL.WITH.VAR.RENAMING))
	      CLAUSE1)
       (EVERY #'(LAMBDA (LITERAL2)
		  (FIND LITERAL2 CLAUSE1 :TEST #'DP=SET.LITERAL.ARE.EQUAL.WITH.VAR.RENAMING))
	      CLAUSE2)))


(DEFUN DP=SET.LITERAL.ARE.EQUAL.WITH.VAR.RENAMING (LITERAL1 LITERAL2)
  
  ;;; Edited : 26.04.94 by CS
  ;;; Input  : two literals
  ;;; Value  : T, iff it could be determined that the two literals are equal under a variable renaming
  
  (LET (MATCHERS)
    (COND ((AND (DP=SET.LITERAL.IS LITERAL1)
		(DP=SET.LITERAL.IS LITERAL2)
		(OR (NOT (EQL (LIST-LENGTH (DP=SET.LITERAL.LEFT.TERMLIST LITERAL1))
			      (LIST-LENGTH (DP=SET.LITERAL.LEFT.TERMLIST LITERAL2))))
		    (NOT (EQL (LIST-LENGTH (DP=SET.LITERAL.RIGHT.TERMLIST LITERAL1))
			      (LIST-LENGTH (DP=SET.LITERAL.RIGHT.TERMLIST LITERAL2))))))
	   NIL)
	  (T (AND (SETQ MATCHERS (UNI-LITERAL.MATCH LITERAL1 LITERAL2))
		  (SOME #'UNI-SUBST.IS.VARIABLE.RENAMING MATCHERS))))))


(DEFUN DP=SET.LITERAL.ARE.EQUAL (LITERAL1 LITERAL2)
  
  ;;; Edited : 26.04.94 by CS
  ;;; Input  : two literals
  ;;; Value  : T, iff it could be determined that the two literals are equal 
  
  (LET (MATCHERS)
    (COND ((AND (DP=SET.LITERAL.IS LITERAL1)
		(DP=SET.LITERAL.IS LITERAL2)
		(OR (NOT (EQL (LIST-LENGTH (DP=SET.LITERAL.LEFT.TERMLIST LITERAL1))
			      (LIST-LENGTH (DP=SET.LITERAL.LEFT.TERMLIST LITERAL2))))
		    (NOT (EQL (LIST-LENGTH (DP=SET.LITERAL.RIGHT.TERMLIST LITERAL1))
			      (LIST-LENGTH (DP=SET.LITERAL.RIGHT.TERMLIST LITERAL2))))))
	   NIL)
	  (T (AND (SETQ MATCHERS (UNI-LITERAL.MATCH LITERAL1 LITERAL2))
		  (SOME #'NULL MATCHERS))))))



(DEFUN DP=SET.LITERAL.IS (LITERAL)
  
  ;;; Edited : 17.02.94 by CS
  ;;; Input  : a literal
  ;;; Value  : determines whether the specified literal is a literal concerning predefined sets

  (LET ((SYMBOL (DA-LITERAL.SYMBOL LITERAL))
	SORT)
    (OR (AND (= (LENGTH (DA-LITERAL.TERMLIST LITERAL)) 1)
	     (SETQ SORT (DA-TERM.SORT (FIRST (DA-LITERAL.TERMLIST LITERAL))))
	     (EQ SYMBOL (DP-PREDICATE.SET.DELTA.SUBSET SORT)))
	(AND (>= (LENGTH (DA-LITERAL.TERMLIST LITERAL)) 2)
	     (SETQ SORT (DA-TERM.SORT (SECOND (DA-LITERAL.TERMLIST LITERAL))))
	     (OR (EQ SYMBOL (DP-PREDICATE.SET.<= SORT))
		 (EQ SYMBOL (DP-PREDICATE.SET.>= SORT))
		 (EQ SYMBOL (DP-PREDICATE.SET.ELEM SORT))
		 (EQ SYMBOL (DP-PREDICATE.SET.DELTA.DELETE SORT))
		 (EQ SYMBOL (DP-PREDICATE.SET.DELTA.INTERSECTION.1 SORT))
		 (EQ SYMBOL (DP-PREDICATE.SET.DELTA.INTERSECTION.2 SORT))
		 (EQ SYMBOL (DP-PREDICATE.SET.DELTA.DIFFERENCE SORT))
		 (AND (EQ SYMBOL (DP-PREDICATE.EQUALITY))
		      (DP-SORT.SET SORT)))))))


(DEFUN DP-SET.LITERAL.IS (LITERAL)

  ;;; Input: a literal
  ;;; Value: determines whether the specified literal is a literal concerning predefined sets

  (DP=SET.LITERAL.IS LITERAL))






;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(DEFUN DP-SET.LITERAL.IS.PREDEFINED (LITERAL)
  
  ;;; Edited : 21.04.94 by CS
  ;;; Input  : a literal
  ;;; Value  : T, iff literal is either equality with both arguments of sort set, or
  ;;;          it is a literal with the predicate being a predefined set predicate
  
  (OR (AND (DA-LITERAL.IS.EQUALITY LITERAL)
	   (DP-SORT.SET (DA-TERM.SORT (FIRST (DA-LITERAL.TERMLIST LITERAL))))
	   (DP-SORT.SET (DA-TERM.SORT (SECOND (DA-LITERAL.TERMLIST LITERAL)))))
      (AND (CDR (DA-LITERAL.TERMLIST LITERAL))
	   (EQ (DA-LITERAL.SYMBOL LITERAL) (DP-PREDICATE.SET.ELEM (DA-TERM.SORT (SECOND (DA-LITERAL.TERMLIST LITERAL))))))
      (AND (DA-LITERAL.TERMLIST LITERAL)
	   (EQ (DA-LITERAL.SYMBOL LITERAL) (DP-PREDICATE.SET.<= (DA-TERM.SORT (FIRST (DA-LITERAL.TERMLIST LITERAL))))))
      (AND (DA-LITERAL.TERMLIST LITERAL)
	   (EQ (DA-LITERAL.SYMBOL LITERAL) (DP-PREDICATE.SET.>= (DA-TERM.SORT (FIRST (DA-LITERAL.TERMLIST LITERAL))))))
      (AND (DA-LITERAL.TERMLIST LITERAL)
	   (EQ (DA-LITERAL.SYMBOL LITERAL) (DP-PREDICATE.SET.DELTA.SUBSET (DA-TERM.SORT (FIRST (DA-LITERAL.TERMLIST LITERAL))))))
      (AND (DA-LITERAL.TERMLIST LITERAL)
	   (EQ (DA-LITERAL.SYMBOL LITERAL) (DP-PREDICATE.SET.DELTA.INTERSECTION.1 (DA-TERM.SORT (FIRST (DA-LITERAL.TERMLIST LITERAL))))))
      (AND (DA-LITERAL.TERMLIST LITERAL)
	   (EQ (DA-LITERAL.SYMBOL LITERAL) (DP-PREDICATE.SET.DELTA.INTERSECTION.2 (DA-TERM.SORT (FIRST (DA-LITERAL.TERMLIST LITERAL))))))
      (AND (DA-LITERAL.TERMLIST LITERAL)
	   (EQ (DA-LITERAL.SYMBOL LITERAL) (DP-PREDICATE.SET.DELTA.DIFFERENCE (DA-TERM.SORT (FIRST (DA-LITERAL.TERMLIST LITERAL))))))
      (AND (CDR (DA-LITERAL.TERMLIST LITERAL))
	   (EQ (DA-LITERAL.SYMBOL LITERAL) (DP-PREDICATE.SET.DELTA.DELETE (DA-TERM.SORT (SECOND (DA-LITERAL.TERMLIST LITERAL))))))))


(DEFUN DP-SET.TERM.IS.PREDEFINED (TERM)
  
  ;;; Edited : 21.04.94 by CS
  ;;; Input  : a term
  ;;; Value  : T, iff the leading function symbol of \verb$TERM$ is a predefined set function
  
  (LET ((SORT (DA-TERM.SORT TERM)))
    (OR (EQ (DA-TERM.SYMBOL TERM) (DP-FUNCTION.SET.EMPTY SORT))
	(EQ (DA-TERM.SYMBOL TERM) (DP-FUNCTION.SET.INSERT SORT))
	(EQ (DA-TERM.SYMBOL TERM) (DP-FUNCTION.SET.SYM.DIFFERENCE SORT))
	(EQ (DA-TERM.SYMBOL TERM) (DP-FUNCTION.SET.SUBSET SORT))
	(EQ (DA-TERM.SYMBOL TERM) (DP-FUNCTION.SET.DELETE SORT))
	(EQ (DA-TERM.SYMBOL TERM) (DP-FUNCTION.SET.UNION SORT))
	(EQ (DA-TERM.SYMBOL TERM) (DP-FUNCTION.SET.INTERSECTION SORT))
	(EQ (DA-TERM.SYMBOL TERM) (DP-FUNCTION.SET.DIFFERENCE SORT)))))



(DEFUN DP-SET.LITERAL.SIMPLIFY (LITERAL)
  
  ;;; Edited : 06.03.94 by CS
  ;;; Input  : a literal
  ;;; Effect : the specified literal is simplified due to certain ``set'' simplification rules
  ;;; Value  : a (possibly) new formula

  (LET (SORT)
    (COND ((AND (DA-LITERAL.IS.EQUALITY LITERAL)
		(DP-SORT.SET (DA-TERM.SORT (FIRST (DA-LITERAL.TERMLIST LITERAL))))
		(DP-SORT.SET (DA-TERM.SORT (SECOND (DA-LITERAL.TERMLIST LITERAL)))))
	   (SETF (FIRST (DA-LITERAL.TERMLIST LITERAL))
		 (DP=SET.SIMPLIFY.NORMALIZED.SET.TERM (DP=SET.NORMALIZE.SET.TERM (FIRST (DA-LITERAL.TERMLIST LITERAL)))))
	   (SETF (SECOND (DA-LITERAL.TERMLIST LITERAL))
		 (DP=SET.SIMPLIFY.NORMALIZED.SET.TERM (DP=SET.NORMALIZE.SET.TERM (SECOND (DA-LITERAL.TERMLIST LITERAL)))))
	   (DP=SET.LITERAL.SIMPLIFY.SET.EQUALITY LITERAL))

	  ((AND (CDR (DA-LITERAL.TERMLIST LITERAL))
		(EQ (DA-LITERAL.SYMBOL LITERAL) (DP-PREDICATE.SET.ELEM (DA-TERM.SORT (SECOND (DA-LITERAL.TERMLIST LITERAL))))))
	   (SETF (FIRST (DA-LITERAL.TERMLIST LITERAL))
		 (DP-SET.NORMALIZE.TERM (FIRST (DA-LITERAL.TERMLIST LITERAL))))
	   (SETF (SECOND (DA-LITERAL.TERMLIST LITERAL))
		 (DP=SET.SIMPLIFY.NORMALIZED.SET.TERM (DP=SET.NORMALIZE.SET.TERM (SECOND (DA-LITERAL.TERMLIST LITERAL)))))
	   (DP=SET.LITERAL.SIMPLIFY.ELEM LITERAL))

	  ((AND (DA-LITERAL.TERMLIST LITERAL)
		(EQ (DA-LITERAL.SYMBOL LITERAL) (DP-PREDICATE.SET.<= (DA-TERM.SORT (FIRST (DA-LITERAL.TERMLIST LITERAL))))))
	   (SETF (FIRST (DA-LITERAL.TERMLIST LITERAL))
		 (DP=SET.SIMPLIFY.NORMALIZED.SET.TERM (DP=SET.NORMALIZE.SET.TERM (FIRST (DA-LITERAL.TERMLIST LITERAL)))))
	   (SETF (SECOND (DA-LITERAL.TERMLIST LITERAL))
		 (DP=SET.SIMPLIFY.NORMALIZED.SET.TERM (DP=SET.NORMALIZE.SET.TERM (SECOND (DA-LITERAL.TERMLIST LITERAL)))))
	   (DP=SET.LITERAL.SIMPLIFY.<= LITERAL))

	  ((AND (DA-LITERAL.TERMLIST LITERAL)
		(EQ (DA-LITERAL.SYMBOL LITERAL) (DP-PREDICATE.SET.>= (DA-TERM.SORT (FIRST (DA-LITERAL.TERMLIST LITERAL))))))
	   (SETF (DA-LITERAL.TERMLIST LITERAL)
		 (REVERSE (DA-LITERAL.TERMLIST LITERAL)))
	   (SETF (FIRST (DA-LITERAL.TERMLIST LITERAL))
		 (DP=SET.SIMPLIFY.NORMALIZED.SET.TERM (DP=SET.NORMALIZE.SET.TERM (FIRST (DA-LITERAL.TERMLIST LITERAL)))))
	   (SETF (SECOND (DA-LITERAL.TERMLIST LITERAL))
		 (DP=SET.SIMPLIFY.NORMALIZED.SET.TERM (DP=SET.NORMALIZE.SET.TERM (SECOND (DA-LITERAL.TERMLIST LITERAL)))))
	   (DP=SET.LITERAL.SIMPLIFY.<= LITERAL))

	  ((AND (DA-LITERAL.TERMLIST LITERAL)
		(EQ (DA-LITERAL.SYMBOL LITERAL) (DP-PREDICATE.SET.DELTA.SUBSET
						 (SETQ SORT (DA-TERM.SORT (FIRST (DA-LITERAL.TERMLIST LITERAL)))))))
	   (DP-SET.LITERAL.SIMPLIFY (DA-LITERAL.CREATE (DA-SIGN.OTHER.SIGN (DA-LITERAL.SIGN LITERAL))
						       (DP-PREDICATE.EQUALITY)
						       (APPEND (DA-LITERAL.TERMLIST LITERAL)
							       (LIST (DA-TERM.CREATE (DP-FUNCTION.SET.EMPTY SORT))))
						       (DA-LITERAL.ATTRIBUTES LITERAL)
						       (DA-LITERAL.COLOURS LITERAL))))

	  ((AND (DA-LITERAL.TERMLIST LITERAL)
		(EQ (DA-LITERAL.SYMBOL LITERAL) (DP-PREDICATE.SET.DELTA.INTERSECTION.1
						 (SETQ SORT (DA-TERM.SORT (FIRST (DA-LITERAL.TERMLIST LITERAL)))))))
	   (DP-SET.LITERAL.SIMPLIFY (DA-LITERAL.CREATE (DA-SIGN.OTHER.SIGN (DA-LITERAL.SIGN LITERAL))
						       (DP-PREDICATE.EQUALITY)
						       (LIST (DA-TERM.CREATE (DP-FUNCTION.SET.INTERSECTION SORT)
									     (DA-LITERAL.TERMLIST LITERAL))
							     (DA-TERM.COPY (FIRST (DA-LITERAL.TERMLIST LITERAL))))
						       (DA-LITERAL.ATTRIBUTES LITERAL)
						       (DA-LITERAL.COLOURS LITERAL))))

	  ((AND (DA-LITERAL.TERMLIST LITERAL)
		(EQ (DA-LITERAL.SYMBOL LITERAL) (DP-PREDICATE.SET.DELTA.INTERSECTION.2
						 (SETQ SORT (DA-TERM.SORT (FIRST (DA-LITERAL.TERMLIST LITERAL)))))))
	   (DP-SET.LITERAL.SIMPLIFY (DA-LITERAL.CREATE (DA-SIGN.OTHER.SIGN (DA-LITERAL.SIGN LITERAL))
						       (DP-PREDICATE.EQUALITY)
						       (LIST (DA-TERM.CREATE (DP-FUNCTION.SET.INTERSECTION SORT)
									     (DA-LITERAL.TERMLIST LITERAL))
							     (DA-TERM.COPY (SECOND (DA-LITERAL.TERMLIST LITERAL))))
						       (DA-LITERAL.ATTRIBUTES LITERAL)
						       (DA-LITERAL.COLOURS LITERAL))))

	  ((AND (DA-LITERAL.TERMLIST LITERAL)
		(EQ (DA-LITERAL.SYMBOL LITERAL) (DP-PREDICATE.SET.DELTA.DIFFERENCE
						 (SETQ SORT (DA-TERM.SORT (FIRST (DA-LITERAL.TERMLIST LITERAL)))))))
	   (DP-SET.LITERAL.SIMPLIFY (DA-LITERAL.CREATE (DA-SIGN.OTHER.SIGN (DA-LITERAL.SIGN LITERAL))
						       (DP-PREDICATE.EQUALITY)
						       (LIST (DA-TERM.CREATE (DP-FUNCTION.SET.DIFFERENCE SORT)
									     (DA-LITERAL.TERMLIST LITERAL))
							     (DA-TERM.COPY (FIRST (DA-LITERAL.TERMLIST LITERAL))))
						       (DA-LITERAL.ATTRIBUTES LITERAL)
						       (DA-LITERAL.COLOURS LITERAL))))

	  ((AND (CDR (DA-LITERAL.TERMLIST LITERAL))
		(EQ (DA-LITERAL.SYMBOL LITERAL) (DP-PREDICATE.SET.DELTA.DELETE
						 (SETQ SORT (DA-TERM.SORT (SECOND (DA-LITERAL.TERMLIST LITERAL)))))))
	   (DP-SET.LITERAL.SIMPLIFY (DA-LITERAL.CREATE (DA-LITERAL.SIGN LITERAL) (DP-PREDICATE.SET.ELEM SORT)
						       (DA-LITERAL.TERMLIST LITERAL)
						       (DA-LITERAL.ATTRIBUTES LITERAL)
						       (DA-LITERAL.COLOURS LITERAL))))

	  (T (SETF (DA-LITERAL.TERMLIST LITERAL)
		   (MAPCAR #'DP-SET.NORMALIZE.TERM (DA-LITERAL.TERMLIST LITERAL)))
	    (EG-EVAL LITERAL)))))


(DEFUN DP-SET.NORMALIZE.TERM (TERM)
  ;;; Edited : 06.03.94 by CS
  ;;; Input  : a term
  ;;; Effect : each subterm is first normalized, then simplified (due to certain ``set'' simplification
  ;;;          rules), and then transformed back into standard term notation
  ;;; Value  : a (possibly) new term

  (COND ((DP-SORT.SET (DA-TERM.SORT TERM))
	 (DP=SET.COMPUTE.SET.TERM (DP=SET.SIMPLIFY.NORMALIZED.SET.TERM (DP=SET.NORMALIZE.SET.TERM (da-term.copy TERM)))))
	(T (SETF (DA-TERM.TERMLIST TERM)
		 (MAPCAR #'DP-SET.NORMALIZE.TERM (DA-TERM.TERMLIST TERM)))
	   (EG-EVAL TERM))))
	  
	 
(DEFUN DP=SET.LITERAL.SIMPLIFY.SET.EQUALITY (LITERAL)
  
  ;;; Edited : 21.04.94 by CS
  ;;; Input  : an equality literal, both arguments are normalized
  ;;; Effect : the equality is simplified due to certain simplification rules
  ;;; Value  : a formula denoting the simplified literal from above
  
  (LET ((LEFT (FIRST (DA-LITERAL.TERMLIST LITERAL)))
	(RIGHT (SECOND (DA-LITERAL.TERMLIST LITERAL)))
	(SORT (DA-TERM.SORT (FIRST (DA-LITERAL.TERMLIST LITERAL))))
	RESULT)
    (COND (; +() = +()
	   (AND (NULL (DA-TERM.TERMLIST LEFT))
		(NULL (DA-TERM.TERMLIST RIGHT)))  
	   (COND ((DA-SIGN.IS.POSITIVE (DA-LITERAL.SIGN LITERAL))
		  (DA-LITERAL.TRUE))
		 (T (DA-LITERAL.FALSE))))
	  (; +() /= +(*(insert(x, y)))
	   (AND (NULL (DA-TERM.TERMLIST LEFT))
		(NULL (CDR (DA-TERM.TERMLIST RIGHT)))
		(NULL (CDR (DA-TERM.TERMLIST (FIRST (DA-TERM.TERMLIST RIGHT)))))
		(EQ (DA-TERM.SYMBOL (FIRST (DA-TERM.TERMLIST (FIRST (DA-TERM.TERMLIST RIGHT)))))
		    (DP-FUNCTION.SET.INSERT SORT))) 
	   (COND ((DA-SIGN.IS.POSITIVE (DA-LITERAL.SIGN LITERAL))
		  (DA-LITERAL.FALSE))
		 (T (DA-LITERAL.TRUE))))
	  (; +(*(insert(x, y))) /= +()
	   (AND (NULL (DA-TERM.TERMLIST RIGHT))
		(NULL (CDR (DA-TERM.TERMLIST LEFT)))
		(NULL (CDR (DA-TERM.TERMLIST (FIRST (DA-TERM.TERMLIST LEFT)))))
		(EQ (DA-TERM.SYMBOL (FIRST (DA-TERM.TERMLIST (FIRST (DA-TERM.TERMLIST LEFT)))))
		    (DP-FUNCTION.SET.INSERT SORT)))
	   (COND ((DA-SIGN.IS.POSITIVE (DA-LITERAL.SIGN LITERAL))
		  (DA-LITERAL.FALSE))
		 (T (DA-LITERAL.TRUE))))
	  (; +() = +(A, B) <-> (+() = A and +() = B)
	   (AND (NULL (DA-TERM.TERMLIST LEFT))
		(NOT (NULL (CDR (DA-TERM.TERMLIST RIGHT)))))
	   (SETQ RESULT (DA-FORMULA.JUNCTION.CLOSURE
			 'AND (MAPCAR #'(LAMBDA (RIGHT.INTERSECTION)
					  (DP=SET.LITERAL.SIMPLIFY.SET.EQUALITY
					   (DA-LITERAL.CREATE (DA-SIGN.PLUS) (DP-PREDICATE.EQUALITY)
							      (LIST (DA-TERM.COPY LEFT)
								    (DA-TERM.CREATE (DP-FUNCTION.SET.UNION SORT)
										    (LIST RIGHT.INTERSECTION))))))
				      (DA-TERM.TERMLIST RIGHT))))
	   (COND ((DA-SIGN.IS.NEGATIVE (DA-LITERAL.SIGN LITERAL))
		  (SETQ RESULT (DA-FORMULA.NEGATE RESULT))))
	   (EG-EVAL (NORM-NORMALIZATION RESULT)))
	  (; +(A, B) \= +() <-> (A = +() and B = +())
	   (AND (NULL (DA-TERM.TERMLIST RIGHT))
		(NOT (NULL (CDR (DA-TERM.TERMLIST LEFT)))))
	   (SETQ RESULT (DA-FORMULA.JUNCTION.CLOSURE
			 'AND (MAPCAR #'(LAMBDA (LEFT.INTERSECTION)
					  (DP=SET.LITERAL.SIMPLIFY.SET.EQUALITY
					   (DA-LITERAL.CREATE (DA-SIGN.PLUS) (DP-PREDICATE.EQUALITY)
							      (LIST (DA-TERM.CREATE (DP-FUNCTION.SET.UNION SORT)
										    (LIST LEFT.INTERSECTION))
								    (DA-TERM.COPY RIGHT)))))
				      (DA-TERM.TERMLIST LEFT))))
	   (COND ((DA-SIGN.IS.NEGATIVE (DA-LITERAL.SIGN LITERAL))
		  (SETQ RESULT (DA-FORMULA.NEGATE RESULT))))
	   (EG-EVAL (NORM-NORMALIZATION RESULT)))
	  (; +(*(insert(x, empty))) = +(*(insert(y, empty))) <-> x = y
	   (AND (NOT (NULL (DA-TERM.TERMLIST LEFT)))
		(NOT (NULL (DA-TERM.TERMLIST RIGHT)))
		(NULL (CDR (DA-TERM.TERMLIST LEFT)))
		(NULL (CDR (DA-TERM.TERMLIST RIGHT)))
		(NULL (CDR (DA-TERM.TERMLIST (FIRST (DA-TERM.TERMLIST LEFT)))))
		(NULL (CDR (DA-TERM.TERMLIST (FIRST (DA-TERM.TERMLIST RIGHT)))))
		(EQ (DA-TERM.SYMBOL (FIRST (DA-TERM.TERMLIST (FIRST (DA-TERM.TERMLIST LEFT))))) (DP-FUNCTION.SET.INSERT SORT))
		(EQ (DA-TERM.SYMBOL (FIRST (DA-TERM.TERMLIST (FIRST (DA-TERM.TERMLIST RIGHT))))) (DP-FUNCTION.SET.INSERT SORT)))
	   (SETQ RESULT (EG-EQUAL (FIRST (DA-TERM.TERMLIST (FIRST (DA-TERM.TERMLIST (FIRST (DA-TERM.TERMLIST LEFT))))))
				  (FIRST (DA-TERM.TERMLIST (FIRST (DA-TERM.TERMLIST (FIRST (DA-TERM.TERMLIST RIGHT))))))
				  NIL))
	   (COND ((AND (DA-LITERAL.IS RESULT)
		       (DA-LITERAL.IS.TRUE RESULT))
		  (COND ((DA-SIGN.IS.POSITIVE (DA-LITERAL.SIGN LITERAL))
			 (DA-LITERAL.TRUE))
			(T (DA-LITERAL.FALSE))))
		 ((AND (DA-LITERAL.IS RESULT)
		       (DA-LITERAL.IS.FALSE RESULT))
		  (COND ((DA-SIGN.IS.POSITIVE (DA-LITERAL.SIGN LITERAL))
			 (DA-LITERAL.FALSE))
			(T (DA-LITERAL.TRUE))))
		 (T (SETF (DA-LITERAL.TERMLIST LITERAL)
			  (LIST (FIRST (DA-TERM.TERMLIST (FIRST (DA-TERM.TERMLIST (FIRST (DA-TERM.TERMLIST LEFT))))))
				(FIRST (DA-TERM.TERMLIST (FIRST (DA-TERM.TERMLIST (FIRST (DA-TERM.TERMLIST RIGHT))))))))
		    (DP-LITERAL.SIMPLIFY
		     (EG-EVAL LITERAL)
		     #'(LAMBDA (COND)
			 (EVERY #'(LAMBDA (LIT) (DA-FORMULA.IS.FALSE (EG-EVAL LIT)))
				COND))))))
	  (; +(A, B) = +(C, D) <-> (A = C or A = D) and (B = C or B = D) and (C = A or C = B) and (D = A or D = B)
	   (AND (NOT (NULL (DA-TERM.TERMLIST LEFT)))
		(NOT (NULL (DA-TERM.TERMLIST RIGHT)))
		(EVERY #'(LAMBDA (LEFT.INTERSECTION)
			   (SOME #'(LAMBDA (RIGHT.INTERSECTION)
				     (DP=SET.INTERSECTION.ARE.EQUAL LEFT.INTERSECTION RIGHT.INTERSECTION))
				 (DA-TERM.TERMLIST RIGHT)))
		       (DA-TERM.TERMLIST LEFT))
		(EVERY #'(LAMBDA (RIGHT.INTERSECTION)
			   (SOME #'(LAMBDA (LEFT.INTERSECTION)
				     (DP=SET.INTERSECTION.ARE.EQUAL LEFT.INTERSECTION RIGHT.INTERSECTION))
				 (DA-TERM.TERMLIST LEFT)))
		       (DA-TERM.TERMLIST RIGHT)))
	   (COND ((DA-SIGN.IS.POSITIVE (DA-LITERAL.SIGN LITERAL))
		  (DA-LITERAL.TRUE))
		 (T (DA-LITERAL.FALSE))))
	  (; +(A, B) \= +(C, D) <-> (A \= C and A \= D) or (B \= C and B \= D) or (C \= A and C \= B) or (D \= A and D \= B)
	   (AND (NOT (NULL (DA-TERM.TERMLIST LEFT)))
		(NOT (NULL (DA-TERM.TERMLIST RIGHT)))
		(OR (SOME #'(LAMBDA (LEFT.INTERSECTION)
			      (EVERY #'(LAMBDA (RIGHT.INTERSECTION)
					 (DP=SET.INTERSECTION.ARE.NOT.EQUAL LEFT.INTERSECTION RIGHT.INTERSECTION))
				     (DA-TERM.TERMLIST RIGHT)))
			  (DA-TERM.TERMLIST LEFT))
		    (SOME #'(LAMBDA (RIGHT.INTERSECTION)
			      (EVERY #'(LAMBDA (LEFT.INTERSECTION)
					 (DP=SET.INTERSECTION.ARE.NOT.EQUAL LEFT.INTERSECTION RIGHT.INTERSECTION))
				     (DA-TERM.TERMLIST LEFT)))
			  (DA-TERM.TERMLIST RIGHT))))
	   (COND ((DA-SIGN.IS.POSITIVE (DA-LITERAL.SIGN LITERAL))
		  (DA-LITERAL.FALSE))
		 (T (DA-LITERAL.TRUE))))
	  (T (SETF (DA-LITERAL.TERMLIST LITERAL)
		   (LIST (DP=SET.COMPUTE.SET.TERM LEFT) (DP=SET.COMPUTE.SET.TERM RIGHT)))
	     (EG-EVAL LITERAL)))))


(DEFUN DP=SET.LITERAL.SIMPLIFY.ELEM (LITERAL)
  
  ;;; Edited : 25.04.94 by CS
  ;;; Input  : a literal in set normal form, denoting elem(x, A)
  ;;; Effect : literal is simplified due to some ``set'' simplification rules
  ;;; Value  : a formula denoting the simplified literal
  
  (LET* ((ELEMENT (FIRST (DA-LITERAL.TERMLIST LITERAL)))
	 (SET (SECOND (DA-LITERAL.TERMLIST LITERAL)))
	 (SET.SORT (DA-TERM.SORT SET))
	 (ELEMENT.SET (DA-TERM.CREATE (DP-FUNCTION.SET.INTERSECTION SET.SORT)
				      (LIST (DA-TERM.CREATE (DP-FUNCTION.SET.INSERT SET.SORT)
							    (LIST ELEMENT (DA-TERM.CREATE (DP-FUNCTION.SET.EMPTY SET.SORT)))))))
	 RESULT)
    (COND (; not elem(x, +())
	   (NULL (DA-TERM.TERMLIST SET))
	   (SETQ RESULT (DA-LITERAL.FALSE)))
	  ((NULL (CDR (DA-TERM.TERMLIST SET)))
	   (COND (; elem(x, +(*(insert(x, empty))))
		  (DP=SET.INTERSECTION.ARE.EQUAL (FIRST (DA-TERM.TERMLIST SET)) ELEMENT.SET)
		  (SETQ RESULT (DP-LITERAL.TRUE)))
		 (; (not x = y) impl (not elem(x, +(*(insert(y, empty)))))
		  (DP=SET.INTERSECTION.ARE.NOT.EQUAL (FIRST (DA-TERM.TERMLIST SET)) ELEMENT.SET)
		  (SETQ RESULT (DA-LITERAL.FALSE)))
		 (; elem(x, insert(y, empty)) <-> x = y
		  (AND (NULL (CDR (DA-TERM.TERMLIST (FIRST (DA-TERM.TERMLIST SET)))))
		       (EQ (DP-FUNCTION.SET.INSERT SET.SORT) (DA-TERM.SYMBOL (FIRST (DA-TERM.TERMLIST (FIRST (DA-TERM.TERMLIST SET)))))))
		  (SETQ RESULT (DP-LITERAL.SIMPLIFY
				(DA-LITERAL.CREATE
				 (DA-SIGN.PLUS) (DP-PREDICATE.EQUALITY)
				 (LIST (DA-TERM.COPY ELEMENT)
				       (FIRST (DA-TERM.TERMLIST (FIRST (DA-TERM.TERMLIST (FIRST (DA-TERM.TERMLIST SET))))))))
				#'(LAMBDA (COND)
				    (EVERY #'(LAMBDA (LIT) (DA-FORMULA.IS.FALSE (EG-EVAL LIT)))
					   COND)))))
		 (; else
		  (NULL (CDR (DA-TERM.TERMLIST (FIRST (DA-TERM.TERMLIST SET)))))
		  (SETQ RESULT (DA-LITERAL.CREATE (DA-SIGN.PLUS) (DP-PREDICATE.SET.ELEM SET.SORT)
						  (LIST ELEMENT (DP=SET.COMPUTE.SET.TERM SET)))))
		 (T ; elem(x, +(*(A, B))) <-> (elem(x, A) and elem(x, B)
		  (SETQ RESULT (DA-FORMULA.JUNCTION.CLOSURE
				'AND (MAPCAR #'(LAMBDA (TERM)
						 (COND ((EQ (DA-TERM.SYMBOL TERM) (DP-FUNCTION.SET.DIFFERENCE SET.SORT))
							(DP=SET.LITERAL.SIMPLIFY.ELEM
							 (DA-LITERAL.CREATE
							  (DA-SIGN.MINUS) (DP-PREDICATE.SET.ELEM SET.SORT)
							  (LIST (DA-TERM.COPY ELEMENT)
								(DA-TERM.CREATE
								 (DP-FUNCTION.SET.UNION SET.SORT)
								 (LIST (DA-TERM.CREATE (DP-FUNCTION.SET.INTERSECTION SET.SORT)
										       (LIST (FIRST (DA-TERM.TERMLIST TERM))))))))))
						       (T (DP=SET.LITERAL.SIMPLIFY.ELEM
							   (DA-LITERAL.CREATE
							    (DA-SIGN.PLUS) (DP-PREDICATE.SET.ELEM SET.SORT)
							    (LIST (DA-TERM.COPY ELEMENT)
								  (DA-TERM.CREATE
								   (DP-FUNCTION.SET.UNION SET.SORT)
								   (LIST (DA-TERM.CREATE (DP-FUNCTION.SET.INTERSECTION SET.SORT)
											 (LIST TERM))))))))))
					     (DA-TERM.TERMLIST (FIRST (DA-TERM.TERMLIST SET)))))))))
	  (T ; elem(x, +(A, B) <-> (elem(x, A) or elem(x, B)
	   (SETQ RESULT
		 (DA-FORMULA.JUNCTION.CLOSURE
		  'OR (MAPCAR #'(LAMBDA (SET.INTERSECTION)
				  (DP=SET.LITERAL.SIMPLIFY.ELEM
				   (DA-LITERAL.CREATE (DA-SIGN.PLUS) (DP-PREDICATE.SET.ELEM SET.SORT)
						      (LIST (DA-TERM.COPY ELEMENT)
							    (DA-TERM.CREATE (DP-FUNCTION.SET.UNION SET.SORT)
									    (LIST SET.INTERSECTION))))))
			      (DA-TERM.TERMLIST SET))))))
    (COND ((DA-SIGN.IS.NEGATIVE (DA-LITERAL.SIGN LITERAL)) (SETQ RESULT (DA-FORMULA.NEGATE RESULT))))
    (EG-EVAL (NORM-NORMALIZATION RESULT))))


(DEFUN DP=SET.LITERAL.SIMPLIFY.<= (LITERAL)
  
  ;;; Edited : 25.04.94 by CS
  ;;; Input  : a literal in set normal form, denoting <=(A, B)
  ;;; Effect : literal is simplified due to some ``set'' simplification rules
  ;;; Value  : a formula denoting the simplified literal
  
  (LET ((LEFT (FIRST (DA-LITERAL.TERMLIST LITERAL)))
	(RIGHT (SECOND (DA-LITERAL.TERMLIST LITERAL)))
	(SORT (DA-TERM.SORT (FIRST (DA-LITERAL.TERMLIST LITERAL))))
	RESULT SPECIFIC.TERM)
    (COND (; <=(+(), B)
	   (NULL (DA-TERM.TERMLIST LEFT))
	   (COND ((DA-SIGN.IS.POSITIVE (DA-LITERAL.SIGN LITERAL))
		  (DA-LITERAL.TRUE))
		 (T (DA-LITERAL.FALSE))))
	  (; <=(A, +()) <-> A = +()
	   (NULL (DA-TERM.TERMLIST RIGHT))
	   (SETF (DA-LITERAL.SYMBOL LITERAL) (DP-PREDICATE.EQUALITY))
	   (DP=SET.LITERAL.SIMPLIFY.SET.EQUALITY LITERAL))
	  (; <=(A, +(*(B, C))) <-> (<=(A, B) and <=(A, C))
	   (AND (NULL (CDR (DA-TERM.TERMLIST RIGHT)))
		(NOT (NULL (CDR (DA-TERM.TERMLIST (FIRST (DA-TERM.TERMLIST RIGHT)))))))
	   (SETQ RESULT (DA-FORMULA.JUNCTION.CLOSURE
			 'AND (MAPCAR #'(LAMBDA (SUBTERM)
					  (COND ((EQ (DA-TERM.SYMBOL SUBTERM) (DP-FUNCTION.SET.DIFFERENCE SORT))
						 (DP=SET.LITERAL.SIMPLIFY.<=
						  (DA-LITERAL.CREATE (DA-SIGN.MINUS) (DP-PREDICATE.SET.<= SORT)
								     (LIST (DA-TERM.COPY LEFT)
									   (DA-TERM.CREATE
									    (DP-FUNCTION.SET.UNION SORT)
									    (LIST (DA-TERM.CREATE
										   (DP-FUNCTION.SET.INTERSECTION SORT)
										   (LIST (FIRST (DA-TERM.TERMLIST SUBTERM))))))))))
						(T (DP=SET.LITERAL.SIMPLIFY.<=
						    (DA-LITERAL.CREATE (DA-SIGN.PLUS) (DP-PREDICATE.SET.<= SORT)
								       (LIST (DA-TERM.COPY LEFT)
									     (DA-TERM.CREATE
									      (DP-FUNCTION.SET.UNION SORT)
									      (LIST (DA-TERM.CREATE
										     (DP-FUNCTION.SET.INTERSECTION SORT)
										     (LIST SUBTERM))))))))))
				      (DA-TERM.TERMLIST (FIRST (DA-TERM.TERMLIST RIGHT))))))
	   (COND ((DA-SIGN.IS.NEGATIVE (DA-LITERAL.SIGN LITERAL))
		  (SETQ RESULT (DA-FORMULA.NEGATE RESULT))))
	   (EG-EVAL (NORM-NORMALIZATION RESULT)))
	  (; <=(+(A, B), C) <-> (<=(A, C) and <=(B, C))
	   (NOT (NULL (CDR (DA-TERM.TERMLIST LEFT))))
	   (SETQ RESULT (DA-FORMULA.JUNCTION.CLOSURE
			 'AND (MAPCAR #'(LAMBDA (SUBTERM)
					  (DP=SET.LITERAL.SIMPLIFY.<=
					   (DA-LITERAL.CREATE (DA-SIGN.PLUS) (DP-PREDICATE.SET.<= SORT)
							      (LIST (DA-TERM.CREATE (DP-FUNCTION.SET.INTERSECTION SORT)
										    (LIST SUBTERM))
								    (DA-TERM.COPY RIGHT)))))
				      (DA-TERM.TERMLIST LEFT))))
	   (COND ((DA-SIGN.IS.NEGATIVE (DA-LITERAL.SIGN LITERAL))
		  (SETQ RESULT (DA-FORMULA.NEGATE RESULT))))
	   (EG-EVAL (NORM-NORMALIZATION RESULT)))
	  (; <=(+(A, B), +(C, D)) <-> ((A = C) or (A = D)) and ((B = C) or (B = D))
	   (EVERY #'(LAMBDA (LEFT.INTERSECTION)
		      (SOME #'(LAMBDA (RIGHT.INTERSECTION)
				(DP=SET.INTERSECTION.ARE.EQUAL LEFT.INTERSECTION RIGHT.INTERSECTION))
			    (DA-TERM.TERMLIST RIGHT)))
		  (DA-TERM.TERMLIST LEFT))
	   (COND ((DA-SIGN.IS.POSITIVE (DA-LITERAL.SIGN LITERAL))
		  (DA-LITERAL.TRUE))
		 (T (DA-LITERAL.FALSE))))
	  (; (not <=(+(A, B), +(C, D))) <-> ((A \= C) and (A \= D)) or ((B \= C) and (B \= D))
	   (SOME #'(LAMBDA (LEFT.INTERSECTION)
		     (EVERY #'(LAMBDA (RIGHT.INTERSECTION)
				(DP=SET.INTERSECTION.ARE.NOT.EQUAL LEFT.INTERSECTION RIGHT.INTERSECTION))
			    (DA-TERM.TERMLIST RIGHT)))
		 (DA-TERM.TERMLIST LEFT))
	   (COND ((DA-SIGN.IS.POSITIVE (DA-LITERAL.SIGN LITERAL))
		  (DA-LITERAL.FALSE))
		 (T (DA-LITERAL.TRUE))))
	  (; <=(+(*(A, B), C), +(B, D)) <-> <=(+(C), +(B, D))
	   (SOME #'(LAMBDA (LEFT.INTERSECTION)
		     (SOME #'(LAMBDA (RIGHT.INTERSECTION)
			       (COND ((DP=SET.INTERSECTION.IS.MORE.SPECIFIC LEFT.INTERSECTION RIGHT.INTERSECTION)
				      (SETQ SPECIFIC.TERM LEFT.INTERSECTION))))
			   (DA-TERM.TERMLIST RIGHT)))
		 (DA-TERM.TERMLIST LEFT))
	   (SETF (DA-TERM.TERMLIST (FIRST (DA-LITERAL.TERMLIST LITERAL)))
		 (DELETE SPECIFIC.TERM (DA-TERM.TERMLIST (FIRST (DA-LITERAL.TERMLIST LITERAL))) :TEST #'UNI-TERM.ARE.EQUAL))
	   (DP=SET.LITERAL.SIMPLIFY.<= LITERAL))
	  (T (SETF (DA-LITERAL.TERMLIST LITERAL)
		   (LIST (DP=SET.COMPUTE.SET.TERM LEFT) (DP=SET.COMPUTE.SET.TERM RIGHT)))
	     (EG-EVAL LITERAL)))))


(DEFUN DP=SET.COMPUTE.SET.TERM (SET)
  
  ;;; Edited : 25.04.94 by CS
  ;;; Input  : a term in set normal form
  ;;; Effect : transforms SET into standard term notation
  ;;; Value  : the term denoted by SET
  
  (LET ((SORT (DA-TERM.SORT SET))
	SINGLETONS NON.SINGLETONS)
    (MAPC #'(LAMBDA (SUBTERM)
	      (COND ((EQ (DA-TERM.SYMBOL SUBTERM) (DP-FUNCTION.SET.INSERT SORT))
		     (SETQ SINGLETONS (CONS SUBTERM SINGLETONS)))
		    (T (SETQ NON.SINGLETONS (CONS SUBTERM NON.SINGLETONS)))))
	  (MAPCAR #'DP=SET.COMPUTE.INTERSECTION (DA-TERM.TERMLIST SET)))
    (DP=SET.GENERATE.UNION SINGLETONS NON.SINGLETONS SORT)))


(DEFUN DP=SET.COMPUTE.INTERSECTION (TERM)
  
  ;;; Edited : 25.04.94 by CS
  ;;; Input  : a term denoting an intersection in set normal form
  ;;; Effect : transforms \verb$TERM$ into standard term notation
  ;;; Value  : the term denoted by \verb$TERM$
  
  (LET ((SORT (DA-TERM.SORT TERM))
	NEG.SINGLETONS NEG.TERMS NON.NEG.TERMS)
    (MAPC #'(LAMBDA (SUBTERM)
	      (COND ((NEQ (DA-TERM.SYMBOL SUBTERM) (DP-FUNCTION.SET.DIFFERENCE SORT))
		     (SETQ NON.NEG.TERMS (CONS SUBTERM NON.NEG.TERMS)))
		    ((EQ (DA-TERM.SYMBOL (FIRST (DA-TERM.TERMLIST SUBTERM))) (DP-FUNCTION.SET.INSERT SORT))
		     (SETQ NEG.SINGLETONS (CONS (FIRST (DA-TERM.TERMLIST SUBTERM)) NEG.SINGLETONS)))
		    (T (SETQ NEG.TERMS (CONS (FIRST (DA-TERM.TERMLIST SUBTERM)) NEG.TERMS)))))
	  (DA-TERM.TERMLIST TERM))
        (DP=SET.GENERATE.DELETE NEG.SINGLETONS (DP=SET.GENERATE.DIFFERENCE (DP=SET.GENERATE.INTERSECTION NON.NEG.TERMS SORT)
									   (DP=SET.GENERATE.UNION NIL NEG.TERMS SORT))
				SORT)))

(DEFUN DP=SET.GENERATE.DIFFERENCE (SET1 SET2)
  ;;; Edited : 25.04.94 by CS
  ;;; Input  : two terms
  ;;; Value  : a term denoting difference(SET1, SET2)
    
  (LET ((SORT (DA-TERM.SORT SET2)))
    (COND ((EQ (DA-TERM.SYMBOL SET2) (DP-FUNCTION.SET.EMPTY SORT))
	   SET1)
	  (T (DA-TERM.CREATE (DP-FUNCTION.SET.DIFFERENCE SORT)
			     (LIST SET1 SET2))))))


(DEFUN DP=SET.GENERATE.UNION (SINGLETONS NON.SINGLETONS SORT)
  
  ;;; Edited : 25.04.94 by CS
  ;;; Input  : a set of singleton terms, a set of non singleton terms, and a sort
  ;;; Value  : a term denoting union(SINGLETONS, NON.SINGLETONS)
    
  (COND ((AND SINGLETONS
	      (NULL NON.SINGLETONS))
	 (DP=SET.GENERATE.UNION (REST SINGLETONS) (LIST (FIRST SINGLETONS)) SORT))
	(SINGLETONS
	 (DA-TERM.CREATE (DP-FUNCTION.SET.INSERT SORT)
			 (LIST (FIRST (DA-TERM.TERMLIST (FIRST SINGLETONS)))
			       (DP=SET.GENERATE.UNION (REST SINGLETONS) NON.SINGLETONS SORT))))
	((NULL NON.SINGLETONS)
	 (DA-TERM.CREATE (DP-FUNCTION.SET.EMPTY SORT)))
	((NULL (REST NON.SINGLETONS))
	 (FIRST NON.SINGLETONS))
	(T (DA-TERM.CREATE (DP-FUNCTION.SET.UNION SORT)
			   (LIST (FIRST NON.SINGLETONS) (DP=SET.GENERATE.UNION NIL (REST NON.SINGLETONS) SORT))))))


(DEFUN DP=SET.GENERATE.INTERSECTION (TERMS SORT)
  
  ;;; Edited : 25.04.94 by CS
  ;;; Input  : a set of terms and a sort
  ;;; Value  : a term denoting intersection(\verb$TERMS$)
    
  (COND ((NULL TERMS) (DA-TERM.CREATE (DP-FUNCTION.SET.EMPTY SORT)))
	((NULL (REST TERMS))
	 (FIRST TERMS))
	(T (DA-TERM.CREATE (DP-FUNCTION.SET.INTERSECTION SORT)
			   (LIST (FIRST TERMS) (DP=SET.GENERATE.INTERSECTION (REST TERMS) SORT))))))


(DEFUN DP=SET.GENERATE.DELETE (SINGLETONS TERM SORT)
  
  ;;; Edited : 25.04.94 by CS
  ;;; Input  : a set of singleton terms, a term, and a sort
  ;;; Value  : a term denoting \verb$TERM$ without all elements of SINGLETONS
    
  (COND ((NULL SINGLETONS) TERM)
	(T (DA-TERM.CREATE (DP-FUNCTION.SET.DELETE SORT)
			   (LIST (FIRST (DA-TERM.TERMLIST (FIRST SINGLETONS)))
				 (DP=SET.GENERATE.DELETE (REST SINGLETONS) TERM SORT))))))

(DEFUN DP=SET.NORMALIZED.SET.TERM.< (TERM1 TERM2)
  
  ;;; Edited : 25.04.94 by CS
  ;;; Input  : two terms
  ;;; Effect : it is determined whether \verb$TERM1$ is smaller than \verb$TERM2$ by comparing their printing
  ;;;          representations
  ;;; Value  : T iff \verb$TERM1$ is smaller than \verb$TERM2$
    
  (LET ((STRINGLIST1 (PR-PRINT.TERM TERM1))
	(STRINGLIST2 (PR-PRINT.TERM TERM2)))
    (DP=SET.STRINGLIST.< STRINGLIST1 STRINGLIST2)))



(DEFUN DP=SET.STRINGLIST.< (STRINGLIST1 STRINGLIST2)
  
  ;;; Edited : 25.04.94 by CS
  ;;; Input  : two lists of strings
  ;;; Value  : T iff STRINGLIST1 is smaller than STRINGLIST2 using the lexicographical order
    
  (COND ((AND (NULL STRINGLIST1) (NULL STRINGLIST2)) NIL)
	((NULL STRINGLIST1) T)
	((NULL STRINGLIST2) NIL)
	(T (LET ((REST.STRING1 (REST STRINGLIST1))
		 (REST.STRING2 (REST STRINGLIST2))
		 (FIRST.STRING1 (FIRST STRINGLIST1))
		 (FIRST.STRING2 (FIRST STRINGLIST2)))
	     (COND ((STRING< FIRST.STRING1 FIRST.STRING2) T)
		   ((STRING> FIRST.STRING1 FIRST.STRING2) NIL)
		   (T (DP=SET.STRINGLIST.< REST.STRING1 REST.STRING2)))))))


(DEFUN DP=SET.SIMPLIFY.NORMALIZED.SET.TERM (TERM)
  
  ;;; Edited : 25.04.94 by CS
  ;;; Input  : a term in set normal form
  ;;; Effect : \verb$TERM$ is simplified and normalized by the following:
  ;;;          simplification by deletion of duplicates and elementary contradictions
  ;;;          normalization using an order on the termlist
  ;;; Value  : a term in set normal form but simplified and normalized
    
  (LET ((SORT (DA-TERM.SORT TERM)))
    (SETF (DA-TERM.TERMLIST TERM)
	  (MAPCAN #'(LAMBDA (SUBTERM)
		      (LET (NEGATED NON.NEGATED)
			(MAPC #'(LAMBDA (SUBSUBTERM)
				  (COND ((EQ (DA-TERM.SYMBOL SUBSUBTERM) (DP-FUNCTION.SET.DIFFERENCE SORT))
					 (SETQ NEGATED (CONS SUBSUBTERM NEGATED)))
					(T (SETQ NON.NEGATED (CONS SUBSUBTERM NON.NEGATED)))))
			      (DA-TERM.TERMLIST SUBTERM))
			(SETQ NON.NEGATED (DELETE-DUPLICATES NON.NEGATED :TEST #'UNI-TERM.ARE.EQUAL))
			(SETQ NEGATED (DELETE-DUPLICATES NEGATED :TEST #'UNI-TERM.ARE.EQUAL))
			(COND ((SOME #'(LAMBDA (NEG.TERM)
					 (FIND-IF #'(LAMBDA (NON.NEG.TERM)
						      (UNI-TERM.ARE.EQUAL NON.NEG.TERM (FIRST (DA-TERM.TERMLIST NEG.TERM))))
						  NON.NEGATED))
				     NEGATED)
			       NIL)
			      (T (SETF (DA-TERM.TERMLIST SUBTERM)
				       (APPEND NON.NEGATED NEGATED))
				 (LIST SUBTERM)))))
		  (DA-TERM.TERMLIST TERM)))
    (SETF (DA-TERM.TERMLIST TERM)
	  (DP=SET.REDUCE.MORE.SPECIFIC.INTERSECTIONS (DA-TERM.TERMLIST TERM)))
    (SETF (DA-TERM.TERMLIST TERM)
	  (SORT (MAPCAR #'(LAMBDA (SUBTERM)
			    (SETF (DA-TERM.TERMLIST SUBTERM)
				  (SORT (DA-TERM.TERMLIST SUBTERM) #'DP=SET.NORMALIZED.SET.TERM.<))
			    SUBTERM)
			(DA-TERM.TERMLIST TERM))
		#'DP=SET.NORMALIZED.SET.TERM.<))
    TERM))


(DEFUN DP=SET.INTERSECTION.IS.MORE.SPECIFIC (SPECIFIC.TERM TERM)
  
  ;;; Edited : 25.04.94 by CS
  ;;; Input  : two intersection terms
  ;;; Effect : it is determined whether SPECIFIC.TERM is more specific than \verb$TERM$
  ;;;          by comparing their termlists
  ;;; Value  : T iff SPECIFIC.TERM is more specific than \verb$TERM$
    
  (EVERY #'(LAMBDA (SUBTERM)
	     (FIND-IF #'(LAMBDA (SPECIFIC.SUBTERM)
			  (UNI-TERM.ARE.EQUAL SPECIFIC.SUBTERM SUBTERM))
		      (DA-TERM.TERMLIST SPECIFIC.TERM)))
	 (DA-TERM.TERMLIST TERM)))


(DEFUN DP=SET.REDUCE.MORE.SPECIFIC.INTERSECTIONS (TERMLIST &OPTIONAL ALREADY)
  
  ;;; Edited : 25.04.94 by CS
  ;;; Input  : a termlist and (optionally) a list of already investigated terms
  ;;; Effect : reduction of more specific terms in \verb$TERMLIST$
  ;;; Value  : a list of terms which does not contain terms that are more specific
    
  (COND ((NULL TERMLIST) ALREADY)
	(T (LET ((TERM (FIRST TERMLIST))
		 (REST.TERMLIST (REST TERMLIST)))
	     (COND ((AND (APPEND REST.TERMLIST ALREADY)
			 (SOME #'(LAMBDA (OTHER.TERM)
				   (DP=SET.INTERSECTION.IS.MORE.SPECIFIC TERM OTHER.TERM))
			       (APPEND REST.TERMLIST ALREADY)))
		    (DP=SET.REDUCE.MORE.SPECIFIC.INTERSECTIONS REST.TERMLIST ALREADY))
		   (T (DP=SET.REDUCE.MORE.SPECIFIC.INTERSECTIONS REST.TERMLIST (CONS TERM ALREADY))))))))


(DEFUN DP=SET.NORMALIZE.SET.TERM (TERM)
  
  ;;; Edited : 25.04.94 by CS
  ;;; Input  : a set term
  ;;; Effect : \verb$TERM$ is transformed into set normal form which is:
  ;;;          +(*($A_1, \ldots, A_n$), *(B, ...), ...) where $A_i$ is either a term of the form
  ;;;          $\tt \setminus$(C) (meaning {\em not} C) or simply C,
  ;;;          and C is either a singleton term or has not a predefined function symbol as leading function symbol
  ;;; Value  : the set normal form of \verb$TERM$ 
    
  (LET ((SORT (DA-TERM.SORT TERM))
	LEFT RIGHT)
    (COND (; +(A, B) = +(A, B)
	   (EQ (DA-TERM.SYMBOL TERM) (DP-FUNCTION.SET.UNION SORT))
	   (SETQ LEFT (DP=SET.NORMALIZE.SET.TERM (FIRST (DA-TERM.TERMLIST TERM))))
	   (SETQ RIGHT (DP=SET.NORMALIZE.SET.TERM (SECOND (DA-TERM.TERMLIST TERM))))
	   (DP=SET.COMPUTE.UNION.TERM LEFT RIGHT))
	  (; *(A, B) = +(*(A, B))
	   (EQ (DA-TERM.SYMBOL TERM) (DP-FUNCTION.SET.INTERSECTION SORT))
	   (SETQ LEFT (DP=SET.NORMALIZE.SET.TERM (FIRST (DA-TERM.TERMLIST TERM))))
	   (SETQ RIGHT (DP=SET.NORMALIZE.SET.TERM (SECOND (DA-TERM.TERMLIST TERM))))
	   (DP=SET.COMPUTE.INTERSECTION.2.TERM LEFT RIGHT))
	  (; $\tt \setminus$(A, B) = +(*(A, $\tt \setminus$(B)))
	   (EQ (DA-TERM.SYMBOL TERM) (DP-FUNCTION.SET.DIFFERENCE SORT))
	   (SETQ LEFT (DP=SET.NORMALIZE.SET.TERM (FIRST (DA-TERM.TERMLIST TERM))))
	   (SETQ RIGHT (DP=SET.NORMALIZE.SET.TERM (SECOND (DA-TERM.TERMLIST TERM))))
	   (COND ((NULL (DA-TERM.TERMLIST RIGHT))
		  LEFT)
		 (T (DP=SET.COMPUTE.INTERSECTION.2.TERM LEFT (DP=SET.COMPUTE.DIFFERENCE.TERM RIGHT)))))
	  (; delete(x, A) = +(*(A, $\tt \setminus$(insert(x, empty))))
	   (EQ (DA-TERM.SYMBOL TERM) (DP-FUNCTION.SET.DELETE SORT))
	   (SETF (DA-TERM.SYMBOL TERM) (DP-FUNCTION.SET.DIFFERENCE SORT))
	   (SETF (DA-TERM.TERMLIST TERM) (LIST (SECOND (DA-TERM.TERMLIST TERM))
					       (DA-TERM.CREATE (DP-FUNCTION.SET.INSERT SORT)
							       (LIST (FIRST (DA-TERM.TERMLIST TERM))
								     (DA-TERM.CREATE (DP-FUNCTION.SET.EMPTY SORT))))))
	   (DP=SET.NORMALIZE.SET.TERM TERM))
	  (; insert(x, empty) = +(*(insert(x, empty)))
	   (AND (EQ (DA-TERM.SYMBOL TERM) (DP-FUNCTION.SET.INSERT SORT))
		(EQ (DA-TERM.SYMBOL (SECOND (DA-TERM.TERMLIST TERM))) (DP-FUNCTION.SET.EMPTY SORT)))
	   (SETF (FIRST (DA-TERM.TERMLIST TERM)) (DP-SET.NORMALIZE.TERM (FIRST (DA-TERM.TERMLIST TERM))))
	   (DA-TERM.CREATE (DP-FUNCTION.SET.UNION SORT)
			   (LIST (DA-TERM.CREATE (DP-FUNCTION.SET.INTERSECTION SORT)
						 (LIST TERM)))))
	  (; insert(x, A) = +(*(insert(x, empty)), A)
	   (EQ (DA-TERM.SYMBOL TERM) (DP-FUNCTION.SET.INSERT SORT))
	   (SETQ LEFT (SECOND (DA-TERM.TERMLIST TERM)))
	   (SETF (SECOND (DA-TERM.TERMLIST TERM)) (DA-TERM.CREATE (DP-FUNCTION.SET.EMPTY SORT)))
	   (DP=SET.NORMALIZE.SET.TERM (DA-TERM.CREATE (DP-FUNCTION.SET.UNION SORT)
						      (LIST LEFT TERM))))
	  (; -(A, B) = +($\tt \setminus$(A, B), $\tt \setminus$(B, A))
	   (EQ (DA-TERM.SYMBOL TERM) (DP-FUNCTION.SET.SYM.DIFFERENCE SORT))
	   (SETQ LEFT (FIRST (DA-TERM.TERMLIST TERM)))
	   (SETQ RIGHT (SECOND (DA-TERM.TERMLIST TERM)))
	   (DP=SET.NORMALIZE.SET.TERM (DA-TERM.CREATE (DP-FUNCTION.SET.UNION SORT)
						      (LIST (DA-TERM.CREATE (DP-FUNCTION.SET.DIFFERENCE SORT)
									    (LIST (DA-TERM.COPY LEFT)
										  (DA-TERM.COPY RIGHT)))
							    (DA-TERM.CREATE (DP-FUNCTION.SET.DIFFERENCE SORT)
									    (LIST RIGHT LEFT))))))
	  (; empty = +()
	   (EQ (DA-TERM.SYMBOL TERM) (DP-FUNCTION.SET.EMPTY SORT))
	   (DA-TERM.CREATE (DP-FUNCTION.SET.UNION SORT)))
	  (T (SETF (DA-TERM.TERMLIST TERM)
		   (MAPCAR #'DP-SET.NORMALIZE.TERM (DA-TERM.TERMLIST TERM)))
	     (DA-TERM.CREATE (DP-FUNCTION.SET.UNION SORT)
			     (LIST (DA-TERM.CREATE (DP-FUNCTION.SET.INTERSECTION SORT)
						   (LIST TERM))))))))


(DEFUN DP=SET.COMPUTE.UNION.TERM (TERM1 TERM2)
  
  ;;; Edited : 25.04.94 by CS
  ;;; Input  : two terms in set normal form
  ;;; Value  : the union of two terms in set normal form
    
  (SETF (DA-TERM.TERMLIST TERM1)
		 (APPEND (DA-TERM.TERMLIST TERM1) (DA-TERM.TERMLIST TERM2)))
  TERM1)


(DEFUN DP=SET.COMPUTE.INTERSECTION.TERM (TERMLIST SORT)
  
  ;;; Edited : 25.04.94 by CS
  ;;; Input  : a list of terms (all in set normal form) and a sort
  ;;; Value  : the intersection of the termlist
    
  (COND ((NULL TERMLIST) (DA-TERM.CREATE (DP-FUNCTION.SET.UNION SORT)))
	((NULL (REST TERMLIST)) (FIRST TERMLIST))
	(T (DP=SET.COMPUTE.INTERSECTION.2.TERM (FIRST TERMLIST)
					       (DP=SET.COMPUTE.INTERSECTION.TERM (REST TERMLIST) SORT)))))
					 
	  


(DEFUN DP=SET.COMPUTE.INTERSECTION.2.TERM (TERM1 TERM2)
  
  ;;; Edited : 25.04.94 by CS
  ;;; Input  : two terms in set normal form
  ;;; Value  : the intersection of the two terms
    
  (LET ((SORT (DA-TERM.SORT TERM1)))
    (DA-TERM.CREATE (DP-FUNCTION.SET.UNION SORT)
		    (MAPCAN #'(LAMBDA (TERM1.INTERSECTION)
				(MAPCAR #'(LAMBDA (TERM2.INTERSECTION)
					    (DA-TERM.CREATE (DP-FUNCTION.SET.INTERSECTION SORT)
							    (DELETE-DUPLICATES
							     (APPEND (MAPCAR #'DA-TERM.COPY (DA-TERM.TERMLIST TERM1.INTERSECTION))
								     (MAPCAR #'DA-TERM.COPY (DA-TERM.TERMLIST TERM2.INTERSECTION)))
							     :TEST #'UNI-TERM.ARE.EQUAL)))
					(DA-TERM.TERMLIST TERM2)))
			    (DA-TERM.TERMLIST TERM1)))))


(DEFUN DP=SET.COMPUTE.DIFFERENCE.TERM (TERM)
  
  ;;; Edited : 25.04.94 by CS
  ;;; Input  : a term in set normal form
  ;;; Value  : computes the ``negation'' of TERM
    
  (LET ((SORT (DA-TERM.SORT TERM)))
    (DP=SET.COMPUTE.INTERSECTION.TERM
     (MAPCAR #'(LAMBDA (TERM.INTERSECTION)
		 (SETF (DA-TERM.SYMBOL TERM.INTERSECTION) (DP-FUNCTION.SET.UNION SORT))
		 (SETF (DA-TERM.TERMLIST TERM.INTERSECTION)
		       (MAPCAR #'(LAMBDA (SUBTERM)
				   (COND ((EQ (DA-TERM.SYMBOL SUBTERM) (DP-FUNCTION.SET.DIFFERENCE SORT))
					  (SETF (DA-TERM.SYMBOL SUBTERM) (DP-FUNCTION.SET.INTERSECTION SORT))
					  SUBTERM)
					 (T (DA-TERM.CREATE (DP-FUNCTION.SET.INTERSECTION SORT)
							    (LIST (DA-TERM.CREATE (DP-FUNCTION.SET.DIFFERENCE SORT)
										  (LIST SUBTERM)))))))
			       (DA-TERM.TERMLIST TERM.INTERSECTION)))
		 TERM.INTERSECTION)
	     (DA-TERM.TERMLIST TERM))
     SORT)))


(DEFUN DP=SET.INTERSECTION.ARE.EQUAL (TERM1 TERM2)
  
  ;;; Edited : 25.04.94 by CS
  ;;; Input  : two intersection terms (in set normal form) of the form *(...)
  ;;; Effect : determines whether the two terms are equal
  ;;; Value  : T, iff both terms are equal
    
  (AND (EVERY #'(LAMBDA (SUBTERM1)
		  (SOME #'(LAMBDA (SUBTERM2)
			    (UNI-TERM.ARE.EQUAL SUBTERM1 SUBTERM2))
			(DA-TERM.TERMLIST TERM2)))
	      (DA-TERM.TERMLIST TERM1))
       (EVERY #'(LAMBDA (SUBTERM2)
		  (SOME #'(LAMBDA (SUBTERM1)
			    (UNI-TERM.ARE.EQUAL SUBTERM1 SUBTERM2))
			(DA-TERM.TERMLIST TERM1)))
	      (DA-TERM.TERMLIST TERM2))))


(DEFUN DP=SET.INTERSECTION.ARE.NOT.EQUAL (TERM1 TERM2)
  
  ;;; Edited : 25.04.94 by CS
  ;;; Input  : two intersection terms (in set normal form) of the form *(...)
  ;;; Effect : determines whether the two terms are not equal
  ;;; Value  : T, iff both terms are not equal
    
  (LET ((SORT (DA-TERM.SORT TERM1))
	RESULT)
    (COND ((AND (>= (LIST-LENGTH (DA-TERM.TERMLIST TERM1)) 1)
		(>= (LIST-LENGTH (DA-TERM.TERMLIST TERM2)) 1))
	   NIL)
	  ((AND (EQL (LIST-LENGTH (DA-TERM.TERMLIST TERM1)) 1)
		(EQ (DA-TERM.SYMBOL TERM1) (DP-FUNCTION.SET.INSERT SORT))
		(OR (SOME #'(LAMBDA (SUBTERM)
			      (AND (EQ (DA-TERM.SYMBOL SUBTERM) (DP-FUNCTION.SET.DIFFERENCE SORT))
				   (EQ (DA-TERM.SYMBOL (FIRST (DA-TERM.TERMLIST SUBTERM)))
				       (DP-FUNCTION.SET.INSERT SORT))
				   (UNI-TERM.ARE.EQUAL (FIRST (DA-TERM.TERMLIST TERM1))
						       (FIRST (DA-TERM.TERMLIST (FIRST (DA-TERM.TERMLIST SUBTERM)))))))
			  (DA-TERM.TERMLIST TERM2))
		    (SOME #'(LAMBDA (SUBTERM)
			      (AND (EQ (DA-TERM.SYMBOL SUBTERM) (DP-FUNCTION.SET.INSERT SORT))
				   (DA-LITERAL.IS (SETQ RESULT (EG-EQUAL (FIRST (DA-TERM.TERMLIST TERM1))
									 (FIRST (DA-TERM.TERMLIST SUBTERM)) NIL)))
				   (DA-LITERAL.IS.FALSE RESULT)))
			  (DA-TERM.TERMLIST TERM2)))))
	  ((AND (EQL (LIST-LENGTH (DA-TERM.TERMLIST TERM2)) 1)
		(EQ (DA-TERM.SYMBOL TERM2) (DP-FUNCTION.SET.INSERT SORT))
		(OR (SOME #'(LAMBDA (SUBTERM)
			      (AND (EQ (DA-TERM.SYMBOL SUBTERM) (DP-FUNCTION.SET.DIFFERENCE SORT))
				   (EQ (DA-TERM.SYMBOL (FIRST (DA-TERM.TERMLIST SUBTERM)))
				       (DP-FUNCTION.SET.INSERT SORT))
				   (UNI-TERM.ARE.EQUAL (FIRST (DA-TERM.TERMLIST TERM2))
						       (FIRST (DA-TERM.TERMLIST (FIRST (DA-TERM.TERMLIST SUBTERM)))))))
			  (DA-TERM.TERMLIST TERM1))
		    (SOME #'(LAMBDA (SUBTERM)
			      (AND (EQ (DA-TERM.SYMBOL SUBTERM) (DP-FUNCTION.SET.INSERT SORT))
				   (DA-LITERAL.IS (SETQ RESULT (EG-EQUAL (FIRST (DA-TERM.TERMLIST TERM2))
									 (FIRST (DA-TERM.TERMLIST SUBTERM)) NIL)))
				   (DA-LITERAL.IS.FALSE RESULT)))
			  (DA-TERM.TERMLIST TERM1))))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(DEFUN DP-ARRAY.LITERAL.IS.PREDEFINED (LITERAL)

  ;;; Edited : 21.04.94 by CS
  ;;; Input  : a literal
  ;;; Value  : T, iff literal is either an equality literal with both argument sorts being an array sort,
  ;;;          or the predicate of literal is a predefined array predicate
  
  (OR (AND (DA-LITERAL.IS.EQUALITY LITERAL)
	   (DP-SORT.ARRAY (DA-TERM.SORT (FIRST (DA-LITERAL.TERMLIST LITERAL))))
	   (DP-SORT.ARRAY (DA-TERM.SORT (SECOND (DA-LITERAL.TERMLIST LITERAL)))))
      (AND (CDR (DA-LITERAL.TERMLIST LITERAL))
	   (EQ (DA-LITERAL.SYMBOL LITERAL) (DP-PREDICATE.ARRAY.ELEM (DA-TERM.SORT (SECOND (DA-LITERAL.TERMLIST LITERAL))))))
      (AND (DA-LITERAL.TERMLIST LITERAL)
	   (EQ (DA-LITERAL.SYMBOL LITERAL) (DP-PREDICATE.ARRAY.DELTA.SUBARRAY (DA-TERM.SORT (FIRST (DA-LITERAL.TERMLIST LITERAL))))))))



(DEFUN DP-ARRAY.TERM.IS.PREDEFINED (TERM)
  
  ;;; Edited : 21.04.94 by CS
  ;;; Input  : a term
  ;;; Value  : T, iff the leading function symbol of term is a predefined array function symbol
  
  (LET ((SORT (DA-TERM.SORT TERM)))
    (OR (EQ (DA-TERM.SYMBOL TERM) (DP-FUNCTION.ARRAY.INIT SORT))
	(EQ (DA-TERM.SYMBOL TERM) (DP-FUNCTION.ARRAY.UPDATE SORT))
	(EQ (DA-TERM.SYMBOL TERM) (DP-FUNCTION.ARRAY.SUBARRAY SORT)))))
	


(DEFUN DP-ARRAY.LITERAL.SIMPLIFY (LITERAL)
  
  ;;; Edited : 06.03.94 by CS
  ;;; Input  : a literal
  ;;; Effect : the specified literal is simplified due to certain ``array'' simplification rules
  ;;; Value  : a (possibly) new formula

  (COND ((AND (DA-LITERAL.IS.EQUALITY LITERAL)
	      (DP-SORT.ARRAY (DA-TERM.SORT (FIRST (DA-LITERAL.TERMLIST LITERAL))))
	      (DP-SORT.ARRAY (DA-TERM.SORT (SECOND (DA-LITERAL.TERMLIST LITERAL)))))
	 (SETF (FIRST (DA-LITERAL.TERMLIST LITERAL))
	       (DP-ARRAY.NORMALIZE.TERM (FIRST (DA-LITERAL.TERMLIST LITERAL))))
	 (SETF (SECOND (DA-LITERAL.TERMLIST LITERAL))
	       (DP-ARRAY.NORMALIZE.TERM (SECOND (DA-LITERAL.TERMLIST LITERAL))))
	 (DP=ARRAY.LITERAL.SIMPLIFY.ARRAY.EQUALITY LITERAL))

	((AND (CDR (DA-LITERAL.TERMLIST LITERAL))
	      (EQ (DA-LITERAL.SYMBOL LITERAL) (DP-PREDICATE.ARRAY.ELEM (DA-TERM.SORT (SECOND (DA-LITERAL.TERMLIST LITERAL))))))
	 (SETF (FIRST (DA-LITERAL.TERMLIST LITERAL))
	       (DP-ARRAY.NORMALIZE.TERM (FIRST (DA-LITERAL.TERMLIST LITERAL))))
	 (SETF (SECOND (DA-LITERAL.TERMLIST LITERAL))
	       (DP-ARRAY.NORMALIZE.TERM (SECOND (DA-LITERAL.TERMLIST LITERAL))))
	 (DP=ARRAY.LITERAL.SIMPLIFY.ELEM LITERAL))

	((AND (DA-LITERAL.TERMLIST LITERAL)
	      (EQ (DA-LITERAL.SYMBOL LITERAL) (DP-PREDICATE.ARRAY.DELTA.SUBARRAY
					       (DA-TERM.SORT (FIRST (DA-LITERAL.TERMLIST LITERAL))))))
	 (SETF (FIRST (DA-LITERAL.TERMLIST LITERAL))
	       (DP-ARRAY.NORMALIZE.TERM (FIRST (DA-LITERAL.TERMLIST LITERAL))))
	 (DP=ARRAY.LITERAL.SIMPLIFY.DELTA.SUBARRAY LITERAL))

	(T (SETF (DA-LITERAL.TERMLIST LITERAL)
		 (MAPCAR #'DP-ARRAY.NORMALIZE.TERM (DA-LITERAL.TERMLIST LITERAL)))
	   (EG-EVAL LITERAL))))


(DEFUN DP=ARRAY.LITERAL.SIMPLIFY.ARRAY.EQUALITY (LITERAL)
  ;;; Edited : 21.04.94 by CS
  ;;; Input  : an equality literal
  ;;; Effect : the equality literal is simplified
  ;;; Value  : the simplified literal
    
  (LET ((LEFT (FIRST (DA-LITERAL.TERMLIST LITERAL)))
	(RIGHT (SECOND (DA-LITERAL.TERMLIST LITERAL)))
	RESULT)
    (COND ((AND (DA-LITERAL.IS (SETQ RESULT (EG-EQUAL LEFT RIGHT NIL)))
		(DA-LITERAL.IS.TRUE RESULT))
	   (COND ((DA-SIGN.IS.POSITIVE (DA-LITERAL.SIGN LITERAL))
		  (DA-LITERAL.TRUE))
		 (T (DA-LITERAL.FALSE))))
	  ((AND (DA-LITERAL.IS RESULT)
		(DA-LITERAL.IS.FALSE RESULT))
	   (COND ((DA-SIGN.IS.POSITIVE (DA-LITERAL.SIGN LITERAL))
		  (DA-LITERAL.FALSE))
		 (T (DA-LITERAL.TRUE))))
	  (T (SETF (DA-LITERAL.TERMLIST LITERAL)
		   (LIST LEFT RIGHT))
	     (EG-EVAL LITERAL)))))


(DEFUN DP=ARRAY.LITERAL.SIMPLIFY.ELEM (LITERAL)
  
  ;;; Edited : 21.04.94 by CS
  ;;; Input  : a literal denoting elem(index, array)
  ;;; Effect : simplification due to elem(index, array) $\tt \leftrightarrow$ (not select(array, index) = default(array))
  ;;; Value  : the simplified literal
    
  (LET ((SORT (DA-TERM.SORT (SECOND (DA-LITERAL.TERMLIST LITERAL))))
	(INDEX (FIRST (DA-LITERAL.TERMLIST LITERAL)))
	(ARR (SECOND (DA-LITERAL.TERMLIST LITERAL))))
    (DP-LITERAL.SIMPLIFY
     (EG-EVAL
      (DA-LITERAL.CREATE (DA-SIGN.OTHER.SIGN (DA-LITERAL.SIGN LITERAL))
			 (DP-PREDICATE.EQUALITY)
			 (LIST (DA-TERM.CREATE (DP-FUNCTION.ARRAY.SELECT SORT)
					       (LIST ARR INDEX))
			       (DA-TERM.CREATE (DP-FUNCTION.ARRAY.DEFAULT SORT)
					       (LIST (DA-TERM.COPY ARR))))))
     #'(LAMBDA (COND)
	 (EVERY #'(LAMBDA (LIT) (DA-FORMULA.IS.FALSE (EG-EVAL LIT)))
		COND)))))


(DEFUN DP=ARRAY.LITERAL.SIMPLIFY.DELTA.SUBARRAY (LITERAL)
  
  ;;; Edited : 21.04.94 by CS
  ;;; Input  : a literal denoting delta.subarray(array)
  ;;; Effect : simplification due to delta.subarray(array) $\tt \leftrightarrow$ (not array = init(default(array)))
  ;;; Value  : the simplified literal
    
  (LET ((SORT (DA-TERM.SORT (FIRST (DA-LITERAL.TERMLIST LITERAL))))
	(ARR (FIRST (DA-LITERAL.TERMLIST LITERAL))))
    (DP=ARRAY.LITERAL.SIMPLIFY.ARRAY.EQUALITY
     (DA-LITERAL.CREATE (DA-SIGN.OTHER.SIGN (DA-LITERAL.SIGN LITERAL))
			(DP-PREDICATE.EQUALITY)
			(LIST (DA-TERM.COPY ARR)
			      (DA-TERM.CREATE (DP-FUNCTION.ARRAY.INIT SORT)
					      (LIST (DA-TERM.CREATE (DP-FUNCTION.ARRAY.DEFAULT SORT)
								    (LIST ARR)))))))))



(DEFUN DP-ARRAY.NORMALIZE.TERM (TERM)
  
  ;;; Edited : 21.04.94 by CS
  ;;; Input  : a term
  ;;; Effect : each subterm of term is simplified due to certain ``array'' simplification rules:
  ;;;          select(A, i) = x impl update(A, i, x) = A
  ;;; Value  : a (possibly) new term
  
  (LET ((SORT (DA-TERM.SORT TERM))
	RESULT)
    (SETQ TERM (EG-EVAL (da-term.copy TERM)))
    (SETF (DA-TERM.TERMLIST TERM)
	  (MAPCAR #'DP-ARRAY.NORMALIZE.TERM (DA-TERM.TERMLIST TERM)))
    (COND ((AND (EQ (DA-TERM.SYMBOL TERM) (DP-FUNCTION.ARRAY.UPDATE SORT))
		(AND (DA-LITERAL.IS (SETQ RESULT (EG-EQUAL (DA-TERM.CREATE (DP-FUNCTION.ARRAY.SELECT SORT)
									   (LIST (FIRST (DA-TERM.TERMLIST TERM))
										 (SECOND (DA-TERM.TERMLIST TERM))))
							   (THIRD (DA-TERM.TERMLIST TERM)) NIL)))
		     (DA-LITERAL.IS.TRUE RESULT)))
	   (EG-EVAL (FIRST (DA-TERM.TERMLIST TERM))))
	  (T (EG-EVAL TERM)))))

