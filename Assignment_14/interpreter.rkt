#lang racket

(require "../chez-init.rkt")
(provide eval-one-exp)

;-------------------+
;                   |
;   sec:DATATYPES   |
;                   |
;-------------------+

;Expression datatype

(define-datatype expression expression?
  [var-exp
   (id symbol?)]
  [lit-exp       
   (datum (lambda (x)
      (ormap 
       (lambda (pred) (pred x))
       (list number? vector? boolean? symbol? string? pair? null?))))]
  [lambda-exp
   (params list?)
   (bodies list?)]
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
   (vars list?) ; list of pair
   (var-exps list?)
   (body list?)]
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
  [app-exp
   (rator expression?)
   (rand (list-of? expression?))])
	

;; environment type definitions

(define scheme-value?
  (lambda (x) #t))
  
(define-datatype environment environment?
  [empty-env-record]
  [extended-env-record
   (syms (list-of? symbol?))
   (vals (list-of? scheme-value?))
   (env environment?)]
  [closure
   (syms (list-of? symbol?))
   (code expression?)
   (env environment?)])


; datatype for procedures.  At first there is only one
; kind of procedure, but more kinds will be added later.

(define-datatype proc-val proc-val?
  [prim-proc
   (name symbol?)]
  [closure-proc
   (syms (list-of? symbol?))
   (code expression?)
   (env environment?)])

  
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
      [((lambda (x)
          (ormap 
           (lambda (pred) (pred x))
           (list number? vector? boolean? symbol? string? null?))) datum)
       (lit-exp datum)]
      [(eqv? (car (quasiquote (unquote datum))) 'quote) (lit-exp (cadr datum))]
      [(pair? datum)
       (cond
         [(eqv? (car datum) 'lambda)
          (unless (> (length datum) 2)  
            (error 'parse-exp "Null lambda body"))  ;Checks for lambda with no body
          (unless (or (symbol? (2nd datum)) (andmap symbol? (2nd datum)))
            (error 'parse-exp "invalid input to lambda"))
          (lambda-exp (2nd datum)
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
          (unless (> (length datum) 2)
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
              (nlet-exp (2nd datum) (map 1st (3rd datum)) (map 2nd (3rd datum)) (parse-exp (cdddr datum)));named let
              (let-exp (map 1st (2nd datum)) (map parse-exp (map 2nd (2nd datum))) (map parse-exp (cddr datum))));regular let
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
                        (map parse-exp (cdr datum)))])]
      
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
                                 (apply-env env sym)))]
      [closure (syms code env) (apply-env env sym)]
      )))


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
    (eval-exp init-env form)))                              ;TODO FIX THIS

; eval-exp is the main component of the interpreter

(define eval-exp
  (lambda (env exp)
    (cases expression exp
      [lit-exp (datum) datum]
      [var-exp (id)
               (apply-env env id)]
      [app-exp (rator rands)
               (let ([proc-value (eval-exp env rator)]
                     [args (eval-rands env rands)])
                 (apply-proc proc-value args))]
      [lambda-exp (vars  bodies)
                  (closure vars bodies env)]
      [set-exp (id init-exp) #t]
      [if-exp (if-cond if-true if-false) (if (eval-exp env if-cond)
                                             (eval-exp env if-true)
                                             (eval-exp env if-false))]
      [ne-if-exp (if-cond if-true) #t]
      [let-exp (vars var-exps bodies)
               (let* ((var-vals (eval-rands env var-exps))
                      (new-env (extend-env vars var-vals env)))
               (last (eval-rands new-env bodies)))]
      [nlet-exp (proc id body) #t]
      [let*-exp (id body) #t]
      [letrec-exp (id body) #t]
      [else (error 'eval-exp "Bad abstract syntax: ~a" exp)])))

; evaluate the list of operands, putting results into a list

(define eval-rands
  (lambda (env rands)
    (map ((curry eval-exp) env) rands)))

;  Apply a procedure to its arguments.
;  At this point, we only have primitive procedures.  
;  User-defined procedures will be added later.

(define apply-proc
  (lambda (proc-value args)
    (cases proc-val proc-value
      [prim-proc (op) (apply-prim-proc op args)]
      [closure-proc (vars code env) (eval-exp (extend-env vars args env) code)]
      ; You will add other cases
      [else (error 'apply-proc
                   "Attempt to apply bad procedure: ~s" 
                   proc-value)])))

(define *prim-proc-names* '(+ - * / not zero? add1 sub1 cons = >=
                              car list cdr null? eq? equal? length list->vector list? pair?
                              vector->list vector? number? symbol? caar cadr cadar procedure?
                              vector vector-set! vector-ref))

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
      [(+) (apply + args)]
      [(-) (apply - args)]
      [(*) (apply * args)]
      [(/) (apply / args)]
      [(add1) (+ (1st args) 1)]
      [(sub1) (- (1st args) 1)]
      [(cons) (cons (1st args) (2nd args))]
      [(=) (= (1st args) (2nd args))]
      [(not) (not (1st args))]
      [(zero?) (zero? (1st args))]
      [(>=) (>= (1st args) (2nd args))]
      [(car) (car (1st args))]
      [(list) (apply list args)]
      [(cdr) (cdr (1st args))]
      [(null?) (null? (1st args))]
      [(eq?) (eq? (1st args) (2nd args))]
      [(equal?) (equal? (1st args) (2nd args))]
      [(length) (length (1st args))]
      [(list->vector) (list->vector (1st args))]
      [(list?) (list? (1st args))]
      [(pair?) (pair? (1st args))]
      [(vector->list) (vector->list (1st args))]
      [(vector?) (vector? (1st args))]
      [(number?) (number? (1st args))]
      [(symbol?) (symbol? (1st args))]
      [(caar) (caar (1st args))]
      [(cadr) (cadr (1st args))]
      [(cadar) (cadar (1st args))]
      [(procedure?) (procedure? (1st args))]
      [(vector) (apply vector args)]
      [(vector-set!) (vector-set! (1st args) (2nd args) (3rd args))]
      [(vector-ref) (vector-ref (1st args) (2nd args))]
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
