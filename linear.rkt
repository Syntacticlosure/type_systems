#lang racket
;; A implementation of Linear Type System
;; from Advanced Topics in Type and Programming Languages


;; qualifiers
(struct llc.lin () #:transparent)
(struct llc.un () #:transparent)
(define llc.qualifier? (or/c llc.lin? llc.un?))
(define/contract (llc.qualifier=? q1 q2)
  (-> llc.qualifier? llc.qualifier? boolean?)
  ;; by #:transparent
  (equal? q1 q2))

(define llc.ty? (flat-named-contract 'llc.ty (λ (x) (or (llc.ty.Bool? x)
                                                        (llc.ty.->? x)
                                                        (llc.ty.*? x)))))

;; terms
(define llc.term? (flat-named-contract
                   'llc.term (λ (x) (or (llc.bool? x)
                                        (llc.pair? x)
                                        (llc.split? x)
                                        (llc.var? x)
                                        (llc.lam? x)
                                        (llc.app? x)
                                        (llc.if? x)))))

;; booleans
(struct/contract llc.true ([q llc.qualifier?]) #:transparent)
(struct/contract llc.false ([q llc.qualifier?]) #:transparent)
(define llc.bool? (or/c llc.true? llc.false?))

;; pairs
(struct/contract llc.pair ([q llc.qualifier?] [fst llc.term?] [snd llc.term?]) #:transparent)

;; pairs elimination
(struct/contract llc.split ([t llc.term?] [x symbol?] [y symbol?] [body llc.term?]) #:transparent)

;; variable
(struct/contract llc.var ([n symbol?]) #:transparent)

;; lambda abstraction
(struct/contract llc.lam ([q llc.qualifier?] [x symbol?] [T llc.ty?] [body llc.term?]) #:transparent)
(struct/contract llc.app ([t1 llc.term?] [t2 llc.term?]) #:transparent)

;; condition
(struct/contract llc.if ([test llc.term?][then llc.term?][else llc.term?]) #:transparent)

;; types
;; pretypes


(struct/contract llc.ty.Bool ([q llc.qualifier?]) #:transparent)
(struct/contract llc.ty.-> ([q llc.qualifier?] [f llc.ty?] [t llc.ty?]) #:transparent)
(struct/contract llc.ty.* ([q llc.qualifier?] [fst llc.ty?] [snd llc.ty?]) #:transparent)

(define/contract (llc.ty=? ty1 ty2)
  (-> llc.ty? llc.ty? boolean?)
  (match* (ty1 ty2)
    [((llc.ty.Bool q1) (llc.ty.Bool q2)) (llc.qualifier=? q1 q2)]
    [((llc.ty.-> q1 f1 t1) (llc.ty.-> q2 f2 t2)) (and (llc.qualifier=? q1 q2)
                                                      (llc.ty=? f1 f2)
                                                      (llc.ty=? t1 t2))]
    [((llc.ty.* q1 fst1 snd1) (llc.ty.* q2 fst2 snd2)) (and (llc.qualifier=? q1 q2)
                                                            (llc.ty=? fst1 snd1)
                                                            (llc.ty=? fst2 snd2))]))

(define/contract (llc.ty.get-qualifier ty)
  (-> llc.ty? llc.qualifier?)
  (match ty
    [(llc.ty.Bool q) q]
    [(llc.ty.-> q _1 _2) q]
    [(llc.ty.* q _1 _2) q]))

(define/contract (llc.ty.check-qualify ty q)
  (-> llc.ty? llc.qualifier? void?)
  (match* ((llc.ty.get-qualifier ty) q)
    [((llc.lin) (llc.un)) (error (format "unrestricted data types should not contain a linear data type: ~a"
                                         (llc.ty.unparse ty)))]
    [(_1 _2) (void)]))
                                         

;; type checking context
(define llc.ty.env? (hash/c symbol? llc.ty?))
(define/contract (llc.ty.env.empty)
  (-> llc.ty.env?)
  (hasheq))

;; T-VAR
(define/contract (llc.ty.env.ref env sym)
  (-> llc.ty.env? symbol? (list/c llc.ty? llc.ty.env?))
  (match (hash-ref env sym #f)
    [#f (error (format "~a: variable not found in typing context: ~a" 'llc.ty.env.ref sym))]
    [ty (match (llc.ty.get-qualifier ty)
          [(llc.lin) (list ty (hash-remove env sym))]
          [(llc.un) (list ty env)])]))

(define/contract (llc.ty.env.set env sym ty)
  (-> llc.ty.env? symbol? llc.ty? llc.ty.env?)
  (hash-set env sym ty))

(define/contract (llc.ty.env.diff env1 env2)
  (-> llc.ty.env? llc.ty.env? llc.ty.env?)
  (for/fold ([env env1])
            ([(v ty) (in-hash env2)])
    (match (llc.ty.get-qualifier ty)
      [(llc.un) (hash-remove env v)] ;; ensure unrestricted variables are removed out of scope
      [(llc.lin) (begin (when (hash-has-key? env v) ;; ensure linear variables are used exactly once
                          (error (format "~a: linear variable ~a remains unused." 'llc.ty.env.diff v)))
                        env)])))

(define/contract (llc.typecheck term env)
  (-> llc.term? llc.ty.env? (list/c llc.ty? llc.ty.env?))
  (match term
    [(or (llc.true q) (llc.false q)) (list (llc.ty.Bool q) env)]
    [(llc.pair q t1 t2) (match-define (list ty1 env1) (llc.typecheck t1 env))
                        (llc.ty.check-qualify ty1 q)
                        (match-define (list ty2 env2) (llc.typecheck t2 env1))
                        (llc.ty.check-qualify ty2 q)
                        (list (llc.ty.* q ty1 ty2) env2)]
    [(llc.var n) (llc.ty.env.ref env n)]
    [(llc.split t v1 v2 body) (match-define (list split-ty env1) (llc.typecheck t env))
                              (match split-ty
                                [(llc.ty.* q ty1 ty2)
                                 (match-define (list ty env2)
                                   (llc.typecheck body
                                                  (llc.ty.env.set (llc.ty.env.set env1 v1 ty1) v2 ty2)))
                                 (list ty (llc.ty.env.diff env2 (hasheq v1 ty1 v2 ty2)))]
                                [_ (error (format "type error in ~a, expected: ~a, but got: ~a"
                                                  (llc.unparse term) 'llc.ty.* (llc.ty.unparse split-ty)))])]
    [(llc.if test then else) (match-define (list test-ty env1) (llc.typecheck test env))
                             (match-define (list then-ty env2) (llc.typecheck then env1))
                             (match-define (list else-ty env3) (llc.typecheck else env1))
                             (unless (llc.ty=? test-ty (llc.ty.Bool))
                               (error (format "type error: expected: Bool, got: ~a, in: ~a" (llc.ty.unparse test-ty)
                                              (llc.unparse term))))
                             (unless (set=? (list->seteq (hash-keys env2))
                                            (list->seteq (hash-keys env3)))
                               (error (format "type context inconsistent in then clause: ~a, and else clause: ~a"
                                              (llc.unparse then) (llc.unparse else))))
                             (unless (llc.ty=? then-ty else-ty)
                               (error (format "type error: different types in then clause: ~a, and else clause: ~a, in term: ~a"
                                              (llc.ty.unparse then-ty)
                                              (llc.ty.unparse else-ty) (llc.unparse term))))
                             (list then-ty env2)]
    [(llc.app t1 t2) (match-define (list ty1 env1) (llc.typecheck t1 env))
                     (match-define (list ty2 env2) (llc.typecheck t2 env1))
                     (match ty1
                       [(llc.ty.-> q f-ty t-ty) (unless (llc.ty=? f-ty ty2)
                                                  (error (format "type error: incorrect argument type: ~a, expected: ~a, in term: ~a"
                                                                 (llc.ty.unparse ty2) (llc.ty.unparse f-ty)
                                                                 (llc.unparse term))))
                                                (list t-ty env2)]
                       [_ (error (format "type error: incorrect function type: ~a, in term: ~a"
                                         (llc.ty.unparse ty1) (llc.unparse term)))])]
    [(llc.lam q x T body) (match-define (list result-ty env1) (llc.typecheck body (llc.ty.env.set env x T)))
                          (define env2 (llc.ty.env.diff env1 (hasheq x T))) ;; ensure x be used or removed
                          (when (and (equal? q (llc.un))
                                     (not (set=? (list->seteq (hash-keys env))
                                                 (list->seteq (hash-keys env2))))) ;; ensure linear variables are not used in unrestricted mode
                            (error (format "linear variables shouldn't be used in an unrestricted lambda. in: ~a"
                                           (llc.unparse term))))
                          (list (llc.ty.-> q T result-ty) env2)]))

(define-match-expander llc.Qualifier
  (λ (stx)
    (syntax-case stx ()
      [(_ q) #`(app llc.qualifier.parse q)])))

(define-match-expander llc.Term
  (λ (stx)
    (syntax-case stx ()
      [(_ q) #`(app llc.parse q)])))

(define-match-expander llc.Ty
  (λ (stx)
    (syntax-case stx ()
      [(_ q) #`(app llc.ty.parse q)])))

(define/contract (llc.qualifier.parse sexp)
  (-> any/c llc.qualifier?)
  (match sexp
    [`un (llc.un)]
    [`lin (llc.lin)]))


(define/contract (llc.parse sexp)
  (-> any/c llc.term?)
  (match sexp
    [(? symbol? s) (llc.var s)]
    [`(,(or 'lin 'un) ,@rst) (match sexp
                               [`(,(llc.Qualifier q) true) (llc.true q)]
                               [`(,(llc.Qualifier q) false) (llc.false q)]
                               [`(,(llc.Qualifier q) pair ,(llc.Term x) ,(llc.Term y)) (llc.pair q x y)]
                               [`(,(llc.Qualifier q) λ (,x ,(llc.Ty T)) ,(llc.Term body)) (llc.lam q x T body)])]
    [`(split ,(llc.Term t) as ,x1 ,x2 in ,(llc.Term body)) (llc.split t x1 x2 body)]
    [`(if ,(llc.Term test) ,(llc.Term then) ,(llc.Term else)) (llc.if test then else)]
    [`(,(llc.Term f) ,(llc.Term arg)) (llc.app f arg)]))

(define/contract (llc.ty.parse sexp)
  (-> any/c llc.ty?)
  (match sexp
    [`(,(llc.Qualifier q) bool) (llc.ty.Bool q)]
    [`(,(llc.Qualifier q) * ,(llc.Ty fst) ,(llc.Ty snd)) (llc.ty.* q fst snd)]
    [`(,(llc.Qualifier q) -> ,(llc.Ty f) ,(llc.Ty t)) (llc.ty.-> q f t)]))

(define/contract (llc.qualifier.unparse q)
  (-> llc.qualifier? any/c)
  (match q
    [(llc.lin) 'lin]
    [(llc.un) 'un]))

(define/contract (llc.ty.unparse ty)
  (-> llc.ty? any/c)
  (match ty
    [(llc.ty.Bool q) `(,(llc.qualifier.unparse q) bool)]
    [(llc.ty.* q fst snd) `(,(llc.qualifier.unparse q) * ,(llc.ty.unparse fst) ,(llc.ty.unparse snd))]
    [(llc.ty.-> q f t) `(,(llc.qualifier.unparse q) -> ,(llc.ty.unparse f) ,(llc.ty.unparse t))]))

(define/contract (llc.unparse term)
  (-> llc.term? any/c)
  (match term
    [(llc.true q) `(,(llc.qualifier.unparse q) true)]
    [(llc.false q) `(,(llc.qualifier.unparse q) false)]
    [(llc.pair q t1 t2) `(,(llc.qualifier.unparse q) ,(llc.unparse t1) ,(llc.unparse t2))]
    [(llc.lam q x T body) `(,(llc.qualifier.unparse q) λ [,x ,(llc.ty.unparse T)] ,(llc.unparse body))]
    [(llc.var n) n]
    [(llc.split t x y body) `(split ,(llc.unparse t) as ,x ,y in ,(llc.unparse body))]
    [(llc.if test then else) `(if ,(llc.unparse test) ,(llc.unparse then) ,(llc.unparse else))]
    [(llc.app f arg) `(,(llc.unparse f) ,(llc.unparse arg))]))

(define/contract (llc.tyck prog)
  (-> any/c any/c)
  (llc.ty.unparse (first (llc.typecheck (llc.parse prog) (hasheq)))))


(llc.tyck `(lin true))
#;(llc.tyck `(lin λ [f (lin -> (lin bool) (lin bool))] (f (f (lin true))))) ;; bad
(llc.tyck `(lin λ [f (un -> (lin bool) (lin bool))] (f (f (lin true)))))
(llc.tyck `(lin λ [f (lin -> (lin bool) (lin bool))] (f (lin true))))
#;(llc.tyck `(lin λ [p (lin * (lin bool) (un bool))] (split p as x y in y))) ;; bad
(llc.tyck `(lin λ [p (lin * (lin bool) (un bool))] (split p as x y in x)))

(llc.tyck `((lin λ [x (lin bool)] x) (lin true)))
#;(llc.tyck `((lin λ [x (lin bool)] x) (un true))) ;; bad
#;(llc.tyck `((lin λ [x (un bool)] x) (lin true))) ;;bad

(llc.tyck `(lin λ [p (un * (lin bool) (lin bool))] p))
;; actually, you could not construct a term has type (un * (lin bool) (lin bool))
#;(llc.tyck `(un pair (lin true) (lin false))) ;; bad

#;(llc.tyck `(lin λ [t (lin bool)] (if (lin true) t (lin true)))) ;; bad

#;(llc.tyck `(un λ [x (lin bool)] (un λ [y (un bool)] x))) ;; unrestricted lambda shouldn't contain linear free vars
(llc.tyck `(un λ [y (lin bool)] y))
