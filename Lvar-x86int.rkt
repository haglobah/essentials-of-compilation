#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
(require "type-check-Lvar.rkt")
(require "type-check-Cvar.rkt")
(require "utilities.rkt")
(require "interp.rkt")
(provide (all-defined-out))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Lint examples
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The following compiler pass is just a silly one that doesn't change
;; anything important, but is nevertheless an example of a pass. It
;; flips the arguments of +. -Jeremy
(define (flip-exp e)
  (match e
    [(Var x) e]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim '- (list e1)) (Prim '- (list (flip-exp e1)))]
    [(Prim '+ (list e1 e2)) (Prim '+ (list (flip-exp e2) (flip-exp e1)))]))

(define (flip-Lint e)
  (match e
    [(Program info e) (Program info (flip-exp e))]))


;; Next we have the partial evaluation pass described in the book.
(define (pe-neg r)
  (match r
    [(Int n) (Int (fx- 0 n))]
    [else (Prim '- (list r))]))

(define (pe-add r1 r2)
  (match* (r1 r2)
    [((Int n1) (Int n2)) (Int (fx+ n1 n2))]
    [(_ _) (Prim '+ (list r1 r2))]))

(define (pe-sub r1 r2)
  (match* (r1 r2)
    [((Int n) (Int m)) (Int (fx- n m))]
    [(_ _) (Prim '- (list r1 r2))]))
   
(define (pe-exp e)
  (match e
    [(Int n) (Int n)]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim '- (list e1)) (pe-neg (pe-exp e1))]
    [(Prim '+ (list e1 e2)) (pe-add (pe-exp e1) (pe-exp e2))]
    [(Prim '- (list e1 e2)) (pe-sub (pe-exp e1) (pe-exp e2))]))

(define (pe-Lint p)
  (match p
    [(Program info e) (Program info (pe-exp e))]))

(define (test-partial-expansion p)
  (assert "testing pe-Lint"
          (equal? (interp-Lint p) (interp-Lint (pe-Lint p)))))
(define (test-pe p)
  #;(print `(program () ,p))
  (test-partial-expansion (parse-program `(program () ,p))))

(test-pe '(+ 10 (- (+ 5 3) (+ 2 2))))
(test-pe '(+ 3 1))
(test-pe '(+ 1 1))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; HW1 Passes
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (uniquify-exp env)
  (lambda (e)
    (match e
      [(Var x)
       (Var (dict-ref env x))]
      [(Int n) (Int n)]
      [(Let x e body)
       (let* ([new-sym (gensym x)]
              [new-env (dict-set env x new-sym)])
        (Let new-sym ((uniquify-exp env) e) ((uniquify-exp new-env) body)))]
      [(Prim op es)
       (Prim op (for/list ([e es]) ((uniquify-exp env) e)))])))

;; uniquify : Lvar -> Lvar
(define (uniquify p)
  (match p
    [(Program info e) (Program info ((uniquify-exp '()) e))]))

(define (rco-atom e)
  (match e
    [(Var x) (values (Var x) '())]
    [(Int n) (values (Int n) '())]
    [(Let x rhs body)
     (define new-rhs (rco-exp rhs))
     (define-values (new-body body-substitutions) (rco-atom body))
     (values new-body (append `((,x . ,new-rhs)) body-substitutions))]
    [(Prim op es)
     (define-values (new-es substitutions-list)
       (for/lists (l1 l2) ([e es]) (rco-atom e)))
     (define substitutions (append* substitutions-list))
     (define tmp (gensym 'tmp))
     (values (Var tmp)
             (append substitutions `((,tmp . ,(Prim op new-es)))))]
    ))

(define (rco-exp e)
  (match e
    [(Var x) (Var x)]
    [(Int x) (Int x)]
    [(Let x rhs body)
     (Let x (rco-exp rhs) (rco-exp body))]
    [(Prim op es)
     (define-values (new-es substitutions-list)
       (for/lists (l m) ([e es]) (rco-atom e)))
     (make-lets (append* substitutions-list) (Prim op new-es))]
    ))

;; remove-complex-opera* : Lvar -> Lvar^mon
(define (remove-complex-opera* p)
  (match p
    [(Program info e)
     (Program info (rco-exp e))]))

(define (explicate-tail e)
  (match e
    [(Var x) (Return (Var x))]
    [(Int n) (Return (Int n))]
    [(Let lhs rhs body)
     (explicate-assign lhs rhs (explicate-tail body))]
    [(Prim op es)
     (Return (Prim op es))]
    [else (error "explicate-tail unhandled case" e)]))

(define (explicate-assign name e cont)
  (match e
    [(Var x) (Seq (Assign (Var name) (Var x)) cont)]
    [(Int n) (Seq (Assign (Var name) (Int n)) cont)]
    [(Let lhs rhs body)
     (explicate-assign lhs rhs (explicate-assign name body cont))]
    [(Prim op es)
     (Seq (Assign (Var name) (Prim op es)) cont)]
    [else (error "explicate-assign unhandled case" e)]))

;; explicate-control : Lvar^mon -> Cvar
(define (explicate-control p)
  (match p
    [(Program info body)
     (CProgram info `((start . ,(explicate-tail body))))]))

(define (select-atm a)
  (match a
    [(Int n) (Imm n)]
    [(Var _) a]))

(define (get-asm op)
  (case op
    [(+) 'addq]
    [(-) 'subq]))

(define/match (select-binary-ops place op a b)
  [((Var v) op (Var w) b) #:when (equal? v w)
   (list (Instr (get-asm op) (select-atm b (Var v))))]
  [((Var v) op a (Var w)) #:when (equal? v w)
   (list (Instr (get-asm op) (select-atm a (Var v))))]
  [(_ _ _ _)
   (list (Instr 'movq (list (select-atm a) place))
         (Instr (get-asm op) (list (select-atm b) place)))])

(define (select-exp place e)
  (match e
    [(or (Int _) (Var _))
     (list (Instr 'movq (list (select-atm e) place)))]
    [(Prim 'read '())
     (list (Callq 'read_int)
           (Instr 'movq (Reg 'rax) place))] ;Can I really do this? What if I want to store things in %rax?
    [(Prim '- (list a))
     (list (Instr 'movq (list (select-atm a) place))
           (Instr 'negq (list place)))]
    [(Prim op (list a b))
     (select-binary-ops place op a b)]
  ))

(define (select-stmt s)
  (match s
    [(Assign place e) (select-exp place e)]))

(define (select-tail t)
  (match t
    [(Seq stmt tail)
     (append (select-stmt stmt) (select-tail tail))]
    [(Return (Prim 'read '()))
     (list (Callq 'read_int) (Jmp 'conclusion))]
    [(Return e)
     (append (select-exp (Reg 'rax) e)
             (list (Jmp 'conclusion)))]))

;; select-instructions : Cvar -> x86var
(define (select-instructions p)
  (match p
    [(CProgram info (list (cons 'start t)))
     (X86Program info (list (cons 'start (Block '() (select-tail t)))))]))
;; assign-homes : x86var -> x86var
(define (assign-homes p)
  (error "TODO: code goes here (assign-homes)"))

;; patch-instructions : x86var -> x86int
(define (patch-instructions p)
  (error "TODO: code goes here (patch-instructions)"))

;; prelude-and-conclusion : x86int -> x86int
(define (prelude-and-conclusion p)
  (error "TODO: code goes here (prelude-and-conclusion)"))

;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `(
     ;; Uncomment the following passes as you finish them.
     ("uniquify" ,uniquify ,interp-Lvar ,type-check-Lvar)
     ("remove complex opera*" ,remove-complex-opera* ,interp-Lvar ,type-check-Lvar)
     ("explicate control" ,explicate-control ,interp-Cvar ,type-check-Cvar)
     ("instruction selection" ,select-instructions ,interp-x86-0)
     ;; ("assign homes" ,assign-homes ,interp-x86-0)
     ;; ("patch instructions" ,patch-instructions ,interp-x86-0)
     ;; ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-0)
     ))
