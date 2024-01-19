#lang racket
(require "adt.rkt")

(adt.together
 (adt tm #:description "term"
      (zero? [e tm?])
      (+ [e1 tm?] [e2 tm?])
      (* [e1 tm?] [e2 tm?])
      (let [x symbol?][e tm?][body tm?])
      (fix [e tm?])
      (lit [c any/c]) ;; constant
      (var [n symbol?]) ;; x
      (lam [x symbol?] [body tm?]) ;; λx.e
      (app [f tm?] [arg tm?]) ;; t1 t2
      (if [test tm?] [then tm?] [else tm?])
      )
 (adt ty #:description "type"
      (var [n symbol?])
      (bool)
      (int)
      (-> [f ty?] [t ty?])
      (all [vars (listof symbol?)] [t ty?])))

(adt option
     (some [x any/c])
     (none))

;; Parsers and UnParsers


(define/contract (tm.parse sexp)
  (-> any/c tm?)
  (define (parse-app apps init)
    (if (null? apps)
        init
        (parse-app (cdr apps) (tm.app init (tm.parse (car apps))))))
  (define (parse-let bds body)
    (if (null? bds)
        body
        (let* ([bd (car bds)]
               [bds* (cdr bds)]
               [x (first bd)]
               [e (second bd)])
          (tm.let x (tm.parse e) (parse-let bds* body)))))
  (match sexp
    [(? symbol? x) (tm.var x)]
    [`(zero? ,e) (tm.zero? (tm.parse e))]
    [`(+ ,t1 ,t2) (tm.+ (tm.parse t1) (tm.parse t2))]
    [`(* ,t1 ,t2) (tm.* (tm.parse t1) (tm.parse t2))]
    [`(fix ,e) (tm.fix (tm.parse e))]
    [`(let ,bds ,body) (parse-let bds (tm.parse body))]
    [`(if ,test ,then ,else) (tm.if (tm.parse test) (tm.parse then) (tm.parse else))]
    [`(λ (,x) ,e) (tm.lam x (tm.parse e))]
    [`(λ (,x ,rst ...) ,e) (tm.lam x (tm.parse `(λ ,rst ,e)))]
    [`(,t1 ,t2 ,t3 ...) ;; left associvity
     (parse-app `(,t2 ,@t3) (tm.parse t1))]
    [_ (tm.lit sexp)]))

(define/contract (tm.unparse tm)
  (-> tm? any/c)
  (define (unparse-lam tm vars)
    (match tm
      [(tm.lam x e) (unparse-lam e (cons x vars))]
      [e `(λ ,(reverse vars) ,(tm.unparse e))]))
  (define (unparse-app apps rhs)
    (match apps
      [(tm.app t1 t2) (unparse-app t1 (cons (tm.unparse t2) rhs))]
      [e (cons (tm.unparse e) rhs)]))
  (match tm
    [(tm.var x) x]
    [(tm.lit x) x]
    [(tm.lam x e) (unparse-lam e (list x))]
    [(tm.zero? e) `(zero? ,(tm.unparse e))]
    [(tm.app t1 t2) (unparse-app t1 (list (tm.unparse t2)))]
    [(tm.+ e1 e2) `(+ ,(tm.unparse e1) ,(tm.unparse e2))]
    [(tm.* e1 e2) `(* ,(tm.unparse e1) ,(tm.unparse e2))]
    [(tm.fix e) `(fix ,(tm.unparse e))]
    [(tm.let x e body) `(let ([,x ,(tm.unparse e)]) ,(tm.unparse body))]
    [(tm.if e1 e2 e3) `(if ,(tm.unparse e1) ,(tm.unparse e2) ,(tm.unparse e3))]))


(define/contract (ty.parse sexp)
  (-> any/c ty?)
  (match sexp
    [`bool (ty.bool)]
    [`int (ty.int)]
    [`(all ,vars ,T) (ty.all vars (ty.parse T))]
    [`(-> ,ty1 ,ty2) (ty.-> (ty.parse ty1) (ty.parse ty2))]
    [`(-> ,ty1 ,ty2 ,tyrst ...) (ty.-> (ty.parse ty1) (ty.parse `(-> ,ty2 ,@tyrst)))]
    [(? symbol? x) (ty.var x)]))

(define/contract (ty.unparse ty)
  (-> ty? any/c)
  (define (unparse-arr ty lhs)
    (match ty
      [(ty.-> f t) (unparse-arr t (cons (ty.unparse f) lhs))]
      [ty `(-> ,@(reverse lhs) ,(ty.unparse ty))]))
  (match ty
    [(ty.bool) `bool]
    [(ty.int) `int]
    [(ty.var n) n]
    [(ty.-> f t) (unparse-arr t (list (ty.unparse f)))]
    [(ty.all vars T) `(all ,vars ,(ty.unparse T))]))

;; type environments
(define ty.env? (hash/c symbol? ty?))

(define/contract (ty.env.ref env x)
  (-> ty.env? symbol? option?)
  (call/ec (λ (bk)
             (option.some (hash-ref env x (λ () (bk (option.none))))))))

(define/contract (ty.env.set env x ty)
  (-> ty.env? symbol? ty? ty.env?)
  (hash-set env x ty))

;; type constraint environment
(define/contract tcenv
  (parameter/c (list/c ty.env? (set/c symbol?) integer?))
  (make-parameter (list (hasheq) (seteq) ;; allocated but unbound tvars
                        0 ;; fresh variable counter
                        )))

(define-syntax-rule (with-tcenv expr)
  (parameterize ([tcenv (list (hasheq) (seteq) 0)])
    expr))

(define/contract (tcenv.fresh)
  (-> ty.var?)
  (match-define (list _1 unbound counter) (tcenv))
  (define sym (string->symbol (format "tvar~a" counter)))
  (tcenv (list _1 (set-add unbound sym)  (add1 counter)))
  (ty.var sym))

(define/contract (tcenv.ref n)
  (-> symbol? option?)
  (match-define (list env _2 _3) (tcenv))
  (ty.env.ref env n))

(define/contract (tcenv.set tvar ty)
  (-> symbol? ty? void?)
  (match-define (list env unbound _3) (tcenv))
  (tcenv (list (hash-set env tvar ty) (set-remove unbound tvar) _3)))

;; normalize
(define/contract (ty.nz ty)
  (-> ty? ty?)
  (match ty
    [(ty.var n) (match (tcenv.ref n)
                  [(option.some t) (ty.nz t)]
                  [(option.none) ty])]
    [(ty.-> f t) (ty.-> (ty.nz f) (ty.nz t))]
    [ty ty]))

;; weak normalize
(define/contract (ty.wnz ty)
  (-> ty? ty?)
  (match ty
    [(ty.var n) (match (tcenv.ref n)
                  [(option.some t) (ty.wnz t)]
                  [(option.none) ty])]
    [ty ty]))

(define/contract (ty.unifyerr ty1 ty2)
  (-> ty? ty? void?)
  (error (format "type error: cannot unify type ~a with type ~a"
                 (ty.unparse ty1)
                 (ty.unparse ty2))))

(define/contract (ty.unify ty1 ty2)
  (-> ty? ty? void?)
  (match* ((ty.wnz ty1) (ty.wnz ty2))
    [((ty.bool) (ty.bool)) (void)]
    [((ty.int) (ty.int)) (void)]
    [((ty.-> f1 t1) (ty.-> f2 t2)) (ty.unify f1 f2)
                                   (ty.unify t1 t2)]
    [((ty.var tvar) ty2) (ty.unifyv tvar ty2)]
    [(ty1 (ty.var tvar)) (ty.unifyv tvar ty1)]
    [(ty1 ty2) (ty.unifyerr ty1 ty2)]))

(define/contract (ty.unifyv tvar ty)
  (-> symbol? ty? void?)
  (match ty
    [(ty.var (== tvar)) (tcenv.set tvar ty)] ;; T == T
    [ty  ;; normalized ty
     (if (ty.occurs tvar ty)
         (ty.unifyerr (ty.var tvar) ty)
         (tcenv.set tvar ty))]))

(define/contract (ty.occurs tvar ty)
  (-> symbol? ty? boolean?)
  (match ty
    [(ty.-> f t) (or (ty.occurs tvar f)
                     (ty.occurs tvar t))]
    [(ty.var n) (match (ty.wnz ty)
                  [(ty.var n) (eqv? tvar n)]
                  [ty (ty.occurs tvar ty)])]
    [ty #f]))

(define/contract (ty.freevars ty)
  (-> ty? (listof symbol?))
  (match ty
    [(ty.-> f t) (append (ty.freevars f) (ty.freevars t))]
    [(ty.var n) (list n)]
    [ty '()]))

(define/contract (ty.generalize ty tvars)
  (-> ty? (listof symbol?) ty?)
  (ty.all tvars ty))

(define/contract (ty.inst ty)
  (-> ty? ty?)
  (define (loop ht ty)
    (match (ty.wnz ty)
      [(ty.var n) (define generic? (hash-ref ht n #f))
                  (if generic? generic? (ty.var n))]
      [(ty.-> f t) (ty.-> (loop ht f) (loop ht t))]
      [ty ty]))
  (match ty
    [(ty.all vars T) (loop (for/hasheq ([v vars])
                             (values v (tcenv.fresh))) T)]
    [ty ty]))

;; tenv: typing context
;; tcenv: typing constraints
(define/contract (typecheck tm tenv)
  (-> tm? ty.env? ty?)
  (match tm
    [(tm.var n) (match (ty.env.ref tenv n)
                  [(option.some ty) (ty.inst ty)]
                  [(option.none) (error (format "variable not found: ~a" n))])]
    [(tm.lam x e) (define tvar (tcenv.fresh))
                  (define result-ty (typecheck e (ty.env.set tenv x tvar)))
                  (ty.-> tvar result-ty)]
    [(tm.app t1 t2) (define ty1 (typecheck t1 tenv))
                    (define ty2 (typecheck t2 tenv))
                    (define tyr (tcenv.fresh))
                    (ty.unify ty1 (ty.-> ty2 tyr))
                    tyr]
    [(or (tm.* e1 e2) (tm.+ e1 e2))
     (define ty1 (typecheck e1 tenv))
     (define ty2 (typecheck e2 tenv))
     (ty.unify ty1 (ty.int))
     (ty.unify ty2 (ty.int))
     (ty.int)]
    [(tm.zero? e)
     (define ty (typecheck e tenv))
     (ty.unify ty (ty.int))
     (ty.bool)]
    [(tm.fix e)
     (define ty (typecheck e tenv))
     (define tvar (tcenv.fresh))
     (ty.unify ty (ty.-> tvar tvar))
     tvar]
    [(tm.if e1 e2 e3) (define ty1 (typecheck e1 tenv))
                      (define ty2 (typecheck e2 tenv))
                      (define ty3 (typecheck e3 tenv))
                      (ty.unify ty1 (ty.bool))
                      (ty.unify ty2 ty3)
                      ty2]
    [(tm.let x e body) (match-define (list _1 unbound-tvars _3) (tcenv))
                       (define ty (ty.nz (typecheck e tenv)))
                       (define tygen (ty.generalize ty (filter (λ (x) (not
                                                                       (ormap (λ (v)
                                                                                (ty.occurs x (ty.nz (ty.var v))))
                                                                               (set->list unbound-tvars))))
                                                               (ty.freevars ty))))
                       (typecheck body (ty.env.set tenv x tygen))]
    [(tm.lit (? integer?)) (ty.int)]
    [(tm.lit (? boolean?)) (ty.bool)]))

(define/contract (tyck sexp)
  (-> any/c any/c)
  (with-tcenv
      (ty.unparse (ty.nz (typecheck (tm.parse sexp) (hasheq))))))

(tyck `(λ (x) x))
(tyck `(λ (f x) (f x)))
(tyck `(λ (x) (+ x 1)))
#;
(tyck `(λ (g) (g g)))

(tyck `(fix (λ (self x)  (if (zero? x) 1 (* x (self (+ x -1)))))))
(tyck `(λ (x) (if #t x 1)))
#;
(tyck `(λ (g) (let ([f (λ (x) (g x))][h (g 1)]) (g #t)))) ;; should not generalize g

(tyck `(let ([id (λ (x) x)][t (id 1)]) (id #t))) ;; let polymorphism