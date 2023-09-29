#lang racket

(require "../chez-init.rkt")
(provide bintree-to-list bintree-add leaf-node interior-node parse-exp unparse-exp)


(define-datatype bintree bintree?
  (leaf-node
   (datum number?))
  (interior-node
   (key symbol?)
   (left-tree bintree?)
   (right-tree bintree?)))

; I've provide this one as a sample to you.
; It's used by the testcases though  so don't mess with it.
(define bintree-to-list
  (lambda (bt)
    (cases bintree bt
      [interior-node (value left right)
                (list value
                      (bintree-to-list left)
                      (bintree-to-list right))]
      [leaf-node (datum)
                 datum])))
                
; Here's the one you need to solve
(define bintree-add
  (lambda (bt num)
    (cases bintree bt
      [leaf-node (datum)
                 (leaf-node (+ datum num))]
      [interior-node (value left right)
                     (interior-node value
                           (bintree-add left num)
                           (bintree-add right num))])))

; This is a parser for simple Scheme expressions, 
; such as those in EOPL, 3.1 thru 3.3.

; You will want to replace this with your parser that includes more expression types, more options for these types, and error-checking.

(define lit-exp?
  (lambda (e)
    (cond [(null? e) #t]
          [(number? e) #t]
          [(list? e) (cond [(eqv? (car e) 'lambda) #f]
                           [(eqv? (car e) 'let) #f]
                           [(eqv? (car e) 'let*) #f]
                           [(eqv? (car e) 'letrec) #f]
                           [(eqv? (car e) 'if) #f]
                           [(eqv? (car e) 'set!) #f]
                           [else #t])]
          [(string? e) #t]
          [(boolean? e) #t]
          [else #f])))

(define-datatype expression expression?
  [var-exp
   (id symbol?)]
  [lit-exp
   (data lit-exp?)]
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
  [app-exp
   (rator expression?)
   (rand expression?)])

; Procedures to make the parser a little bit saner.
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
          (unless (> (length datum) 2)  ;TODO check
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

(define unparse-exp
  (lambda (exp)
    (cases expression exp
      [var-exp (id) id]
      [lit-exp (id) id]
      [lambda-exp (id body) (cons 'lambda (cons id (unparse-exp body)))]
      [set-exp (id init-set) (list 'set! id (unparse-exp init-set))]
      [if-exp (if-cond if-true if-false) (list 'if (unparse-exp if-cond) (unparse-exp if-true) (unparse-exp if-false))]
      [ne-if-exp (if-cond if-true) (list 'if (unparse-exp if-cond) (unparse-exp if-true))]
      [let-exp (id body) (cons 'let (cons id (unparse-exp body)))]
      [nlet-exp (proc id body) (list 'let proc id (unparse-exp body))]
      [let*-exp (id body) (cons 'let* (cons id (unparse-exp body)))]
      [letrec-exp (id body) (cons 'letrec (cons id (unparse-exp body)))]
      [app-exp (rator rand) (list (unparse-exp rator) (unparse-exp rand))])))
      

; An auxiliary procedure that could be helpful.
(define var-exp?
  (lambda (x)
    (cases expression x
      [var-exp (id) #t]
      [else #f])))

;;--------  Used by the testing mechanism   ------------------

(define-syntax nyi
  (syntax-rules ()
    ([_]
     [error "nyi"])))
