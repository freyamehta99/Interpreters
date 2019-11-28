#lang racket
(require eopl/eopl)
(provide (all-defined-out))
(require rackunit)
;;; ===========================================
;;; Abstract Syntax for the language FUNCTIONAL
;;; ===========================================

;;; <ast> ::= <num-ast> |
;;;           <bool-ast> |
;;;           <id-ref-ast> |
;;;           <ifte-ast> |
;;;           <assume-ast> |
;;;           <function-ast> |
;;;           <app-ast>


;;; <num-ast>  ::= (number <number>)
;;; <bool-ast> ::= (boolean <boolean>)
;;; <assume-ast>   ::=(assume ((<id> <ast>) ...) <ast>)
;;; <id-ref-ast>   ::= (id-ref <id>)
;;; <id>           ::= <symbol>
;;; <ifte-ast>     ::= (ifte <ast> <ast> <ast>)
;;; <function-ast> ::= (function (<id> ... ) <ast>)
;;; <app-ast>      ::= (app  <ast>  <ast> ...)
(provide (all-defined-out))
;================
(define-datatype ast ast?
  [number (datum number?)]
  [boolean (datum boolean?)]
  [ifte (test ast?) (then ast?) (else-ast ast?)]
  [function
   (formals (list-of id?))
   (body ast?)]
  [app (rator ast?) (rands (list-of ast?))]
  [id-ref (sym id?)]
  [assume (binds  (list-of bind?)) (body ast?)])

(define-datatype bind bind?
  [make-bind (b-id id?) (b-ast ast?)])

;;; bind-id : bind? -> id?
(define bind-id
  (lambda (b)
    (cases bind b
      [make-bind (b-id b-ast) b-id])))

;;; bind-ast : bind? -> ast?
(define bind-ast
  (lambda (b)
    (cases bind b
      [make-bind (b-id b-ast) b-ast])))

(define id? symbol?)

;;; =========================================
;;; Procedural representation of environments
;;; =========================================

(define env? procedure?)

(define lookup-env
  (lambda (e x)
    (e x)))

;;; empty-env : () -> env?
(define empty-env
  (lambda ()
    (lambda (x)
      (error 'empty-env "unbound identifier ~a" x))))

;;; extended-env :
;;;    [(list-of symbol?) (list-of any/c) env?] -> env?
(define extended-env
  (lambda (syms vals outer-env)
    (lambda (x)
      (let ([j (list-index syms x)])
        (cond
          [(= j -1) (lookup-env outer-env x)]
          [#t (list-ref vals j)])))))

;;; Returns the loction of the element in a list, -1 if the
;;; element is absent.

;;; list-index : [(listof any/c)  any/c] -> 
(define list-index
  (lambda (ls a)
    (letrec ([loop
               (lambda (ls ans)
                 (cond
                   [(null? ls) -1]
                   [(eq? (first ls) a) ans]
                   [#t (loop (rest ls) (+ 1 ans))]))])
      (loop ls 0))))


(define-datatype proc proc?
  [prim-proc
    ;; prim refers to a scheme procedure
    (prim procedure?)
    ;; sig is the signature
    (sig (list-of procedure?))] 
  [closure
    (formals (list-of symbol?))
    (body ast?)
    (env env?)])

;;; prim? : proc? -> boolean?
(define prim-proc?
  (lambda (p)
    (cases proc p
      [prim-proc (prim sig) #t]
      [else #f])))

(define closure? 
  (lambda (p)
    (cases proc p
      [prim-proc (prim sig) #f]
      [else #t])))

 (define expressible-value?
    (or/c number? boolean? proc?))
  
  
  (define denotable-value?
    (or/c number? boolean? proc?))

;;; =====================================
;;; Evaluator for the language FUNCTIONAL
;;; =====================================

;;; eval-ast : [ast? env?]-> expressible-value?
;;; eval-ast :  throws error

(define eval-ast
  (lambda (a env)
    (cases ast a
      [number (datum) datum]
      [boolean (datum) datum]
      [id-ref (sym) (lookup-env env sym)]
      [ifte (test then else-ast)
        (let([b (eval-ast test env)])
          (if (boolean? b)
            (eval-ast (if b then else-ast) env)
            (error 'eval-ast "ifte test is not a boolean ~a" a)))]

      [function (formals body)
          (closure formals body env)]
      [app (rator rands)
        (let ([p (eval-ast rator env)]
              [args (map
                      (lambda (rand)
                        (eval-ast rand env))
                      rands)])
          (if (proc? p)
            (apply-proc p args)
            (error 'eval-ast "application rator is not a proc ~a" a)))]
      
      [assume (binds body)
        (let* ([ids  (map bind-id binds)]
               [asts (map bind-ast binds)]
               [vals (map (lambda (a)
                            (eval-ast a env))
                          asts)]
               [new-env
                (extended-env ids vals env)])
          (eval-ast body new-env))]
      [else (error 'eval-ast "unable to handle some ast cases")])))




;;; apply-proc :
;;;  [proc? (list-of expressible-value?)]
;;;    -> expressible-value?

(define apply-proc
  (lambda (p args)
    (cases proc p
      [prim-proc (prim sig)
        (apply-prim-proc prim sig args)]
      
      [closure (formals body env)
        (apply-closure formals body env args)])))

(define apply-prim-proc
    (lambda (prim sig args)
      (let* ([args-sig (rest sig)])
        (cond
         [(and
            (= (length args-sig) (length args))
            (andmap match-arg-type args-sig args))
          (apply prim  args)]
         [#t (error 'apply-prim-proc
               "incorrect number or type of arguments to ~a"
               prim)]))))

;;; match-arg-type : [procedure? any/c] -> boolean?
(define match-arg-type
  (lambda (arg-type val)
    (arg-type val)))

;;; fix the signature and cleanup the definition of
;;; apply-closure given as a dummy below
  (define apply-closure
    (lambda (formals body env args)
      (let ([new-env (extended-env formals args env)])
        (eval-ast body new-env))))

;;; ==================================
;;; Parser for the language FUNCTIONAL
;;; ==================================

(require racket/match)

(define *keywords*
  '(ifte fn let))

(define idn?
  (lambda (x)
    (and
     (symbol? x)
     (not (memq x *keywords*)))))
         
(define parse
  (lambda (d)
    (match d
     [(? number? n) (number n)]
     [(? boolean? b) (boolean b)]
     [(? idn? x) (id-ref x)]
     [(list 'ifte a b c)  (ifte (parse a) (parse b) (parse c))]

     [(list 'let
        (list (list (? idn? x) e) ...) body)
      (let* ([a (map parse e)]
             [b (map make-bind x a)])
        (assume b (parse body)))]
     
     [(list
         'fn
         (list (? idn? x) ...)
         body)
        (function x (parse body))]
      
      [(list rator rands ...)
        (let* ([rator (parse rator)]
               [rands (map parse rands)])
          (app rator rands))]
     
     [_ (error 'parse "don't know how to parse ~a" d)])))


;;;===========================
;;; Run the interpreter
;;;===========================

(define nonzero? (and/c number? (not/c zero?)))

 (define +p
   (prim-proc +
     (list
       number? ; result type
       number? ; argument-1 type
       number? ; argument-2 type
       )))

(define -p
    (prim-proc -
      (list number? number? number?)))
  
  (define *p
    (prim-proc *
      (list number? number? number?)))
  
  (define /p
    (prim-proc /
      (list number? number? nonzero?)))

  (define <p
    (prim-proc  <
      (list boolean? number? number?)))
  
  (define >p
    (prim-proc  >
      (list boolean? number? number?)))

  (define <=p
    (prim-proc   <=
      (list boolean? number? number?)))

  (define >=p
    (prim-proc   >=
      (list boolean? number? number?)))
  
  (define eq?p
    (prim-proc eq?
      (list boolean? expressible-value? expressible-value?)))
  
  (define 0?p
    (prim-proc zero?
      (list boolean? number?)))

  (define =p
    (prim-proc =
      (list boolean? number? number?)))

  (define !=
    (lambda (thing1 thing2)
      (not (eq? thing1 thing2))))

  (define !=p
    (prim-proc !=
               (list boolean? number? number?)))



(define *init-env*
    (extended-env
     '(+ - * / < > <= >= eq? 0? = !=)
     (list +p -p *p /p <p >p <=p >=p eq?p 0?p =p !=p)
     (empty-env)))


;;; run: ast? -> expressible-value?
(define run
  (lambda (ast)
    (eval-ast (parse ast) *init-env*)))
