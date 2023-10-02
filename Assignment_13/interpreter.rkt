#lang racket

(require "../chez-init.rkt")
(provide eval-one-exp)

;-------------------+
;                   |
;   sec:DATATYPES   |
;                   |
;-------------------+

;Expression datatype

(define lit-exp?
  (lambda (x)
      (ormap 
       (lambda (pred) (pred x))
       (list number? vector? boolean? symbol? string? pair? null?))))

(define-datatype expression expression?
  [var-exp
   (id symbol?)]
  ;[lit-exp
  ; (data lit-exp?)]
  [lambda-exp
   (id (lambda (x) (or (list? x) (symbol? x))))
   (body expression?)]
  [set-exp
   (id symbol?)
   (init-exp expression?)]
  [if-exp
   (if-cond expression?)
   (if-true expression?)
   (if-false expression?)]
  [ne-if-exp
   (if-cond expression?)
   (if-true expression?)]
  [let-exp
   (id list?) ; list of pair
   (body expression?)]
  [nlet-exp
   (proc symbol?)
   (id list?)
   (body expression?)]
  [let*-exp
   (id list?) ; list of pairs
   (body expression?)]
  [letrec-exp
   (id list?) ; lambda statement in here
   (body expression?)]
  [lit-exp       
   (datum lit-exp?)]
  [app-exp
   (rator expression?)
   (rand expression?)])
	

;; environment type definitions

(define scheme-value?
  (lambda (x) #t))
  
(define-datatype environment environment?
  [empty-env-record]
  [extended-env-record
   (syms (list-of? symbol?))
   (vals (list-of? scheme-value?))
   (env environment?)])


; datatype for procedures.  At first there is only one
; kind of procedure, but more kinds will be added later.

(define-datatype proc-val proc-val?
  [prim-proc
   (name symbol?)])

  
;-------------------+
;                   |
;    sec:PARSER     |
;                   |
;-------------------+

; This is a parser for simple Scheme expressions, such as those in EOPL 3.1 thru 3.3.

; You will want to replace this with your parser that includes more expression types, more options for these types, and error-checking.

; Helper procedures to make the parser a little bit saner.

; Again, you'll probably want to use your code from A11b

(define 1st car)
(define 2nd cadr)
(define 3rd caddr)
(define 4th cadddr)

(define parse-exp         
  (lambda (datum)
    (cond
      [(symbol? datum) (var-exp datum)]
      [(lit-exp? datum) (lit-exp datum)]
      [(pair? datum)
       (cond
         [(eqv? (car datum) 'lambda)
          (unless (> (length datum) 2)  
            (error 'parse-exp "Null lambda body"))  ;Checks for lambda with no body
          (unless (or (symbol? (2nd datum)) (andmap symbol? (2nd datum)))
            (error 'parse-exp "invalid input to lambda"))
          (lambda-exp (2nd  datum)
                      (parse-exp (cddr datum)))]
         [(eqv? (car datum) 'set!)         ;parse set!
          (unless (symbol? (second datum))
            (error 'parse-exp "Illegal set! identifier"))
          (unless (= (length datum) 3)
            (error 'parse-exp "invalid number of set inputs"))
          (set-exp
           (second datum)
           (parse-exp (third datum)))]
         [(eqv? (car datum) 'if)
          (unless (< (length datum) 2)
            (error 'parse-exp "Missing if body"))
          (if (= (length datum) 3)
               (ne-if-exp (parse-exp (2nd datum))
                  (parse-exp (3rd datum)))
               (if-exp (parse-exp (2nd datum))
                  (parse-exp (3rd datum))
                  (parse-exp (4th datum))))]
         [(eqv? (1st datum) 'let)
          (unless  (list? (2nd datum))
            (error 'parse-exp "invalid let argument"))
          (unless (> (length datum) 2) 
            (error 'parse-exp "Null let body"))
           (unless (andmap list? (2nd datum))
            (error 'parse-exp "invalid input to let"))
           (unless (andmap (lambda (x) (= (length x) 2)) (2nd datum))
             (error 'parse-exp "invalid input assignment in let"))
            (unless (andmap (lambda (x) (and (symbol? (1st x)) (parse-exp (2nd x)))) (2nd datum))
            (error 'parse-exp "invalid input to let"))

          (if (string? (2nd datum))
              (nlet-exp (2nd datum) (3rd datum) (parse-exp (cdddr datum)));named let
              (let-exp (2nd datum) (parse-exp (cddr datum))));regular let
                                      ]
         [(eqv? (1st datum) 'let*)
          (unless (list? (2nd datum))
            (error 'parse-exp "invalid let argument"))
          (unless (andmap (lambda (x) (= (length x) 2)) (2nd datum))
             (error 'parse-exp "invalid input assignment in let"))
          (unless (> (length datum) 2) 
            (error 'parse-exp "Null let* body"))
           (unless (andmap (lambda (x) (and (symbol? (1st x)) (parse-exp (2nd x)))) (2nd datum))
            (error 'parse-exp "invalid input to let"))
          (let*-exp (2nd datum)
          (parse-exp (cddr datum)))]
         [(eqv? (1st datum) 'letrec)
          (unless (and (list? (2nd datum)) (andmap (lambda (x) (= (length x) 2)) (2nd datum)))
            (error 'parse-exp "invalid let argument"))
          (unless (> (length datum) 2) 
            (error 'parse-exp "Null let body"))
          (unless (andmap (lambda (x) (and (symbol? (1st x)) (parse-exp (2nd x)))) (2nd datum))
            (error 'parse-exp "invalid input to let"))
          (letrec-exp (2nd datum)
          (parse-exp (cddr datum)))]
         [(not (list? datum))
          (error 'parse-exp "invalid list")]
         [else (app-exp (parse-exp (1st datum))
                        (parse-exp (2nd datum)))])]
      
      [else (error 'parse-exp "bad expression: ~s" datum)])))

;-------------------+
;                   |
; sec:ENVIRONMENTS  |
;                   |
;-------------------+


; Environment definitions for CSSE 304 Scheme interpreter.  
; Based on EoPL sections 2.2 and 2.3

(define empty-env
  (lambda ()
    (empty-env-record)))

(define extend-env
  (lambda (syms vals env)
    (extended-env-record syms vals env)))

(define list-find-position
  (lambda (sym los)
    (let loop ([los los] [pos 0])
      (cond [(null? los) #f]
            [(eq? sym (car los)) pos]
            [else (loop (cdr los) (add1 pos))]))))
	    
(define apply-env
  (lambda (env sym) 
    (cases environment env 
      [empty-env-record ()      
                        (error 'env "variable ~s not found." sym)]
      [extended-env-record (syms vals env)
                           (let ((pos (list-find-position sym syms)))
                             (if (number? pos)
                                 (list-ref vals pos)
                                 (apply-env env sym)))])))


;-----------------------+
;                       |
;  sec:SYNTAX EXPANSION |
;                       |
;-----------------------+

; To be added in assignment 14.

;---------------------------------------+
;                                       |
; sec:CONTINUATION DATATYPE and APPLY-K |
;                                       |
;---------------------------------------+

; To be added in assignment 18a.


;-------------------+
;                   |
;  sec:INTERPRETER  |
;                   |
;-------------------+

; top-level-eval evaluates a form in the global environment

(define top-level-eval
  (lambda (form)
    ; later we may add things that are not expressions.
    (eval-exp form)))

; eval-exp is the main component of the interpreter

(define eval-exp
  (lambda (exp)
    (cases expression exp
      [lit-exp (datum) datum]
      [var-exp (id)
               (apply-env init-env id)]
      [app-exp (rator rands)
               (let ([proc-value (eval-exp rator)]
                     [args (eval-rands rands)])
                 (apply-proc proc-value args))]
      [else (error 'eval-exp "Bad abstract syntax: ~a" exp)])))

; evaluate the list of operands, putting results into a list

(define eval-rands
  (lambda (rands)
    (map eval-exp rands)))

;  Apply a procedure to its arguments.
;  At this point, we only have primitive procedures.  
;  User-defined procedures will be added later.

(define apply-proc
  (lambda (proc-value args)
    (cases proc-val proc-value
      [prim-proc (op) (apply-prim-proc op args)]
      ; You will add other cases
      [else (error 'apply-proc
                   "Attempt to apply bad procedure: ~s" 
                   proc-value)])))

(define *prim-proc-names* '(+ - * add1 sub1 cons =))

(define init-env         ; for now, our initial global environment only contains 
  (extend-env            ; procedure names.  Recall that an environment associates
   *prim-proc-names*   ;  a value (not an expression) with an identifier.
   (map prim-proc      
        *prim-proc-names*)
   (empty-env)))

; Usually an interpreter must define each 
; built-in procedure individually.  We are "cheating" a little bit.

(define apply-prim-proc
  (lambda (prim-proc args)
    (case prim-proc
      [(+) (+ (1st args) (2nd args))]
      [(-) (- (1st args) (2nd args))]
      [(*) (* (1st args) (2nd args))]
      [(add1) (+ (1st args) 1)]
      [(sub1) (- (1st args) 1)]
      [(cons) (cons (1st args) (2nd args))]
      [(=) (= (1st args) (2nd args))]
      [else (error 'apply-prim-proc 
                   "Bad primitive procedure name: ~s" 
                   prim-proc)])))

(define rep      ; "read-eval-print" loop.
  (lambda ()
    (display "--> ")
    ;; notice that we don't save changes to the environment...
    (let ([answer (top-level-eval (parse-exp (read)))])
      ;; TODO: are there answers that should display differently?
      (pretty-print answer) (newline)
      (rep))))  ; tail-recursive, so stack doesn't grow.

(define eval-one-exp
  (lambda (x) (top-level-eval (parse-exp x))))
