#lang racket
;; A implementation of λLF
;; from Advanced Topics in Type and Programming Languages

(define llf.term? (flat-named-contract 'llf.term (λ (x) (or (llf.var? x)
                                                            (llf.lam? x)
                                                            (llf.app? x)))))
(define llf.ty? (flat-named-contract 'llf.type (λ (x) (or (llf.ty.var? x)
                                                          (llf.ty.app? x)
                                                          (llf.ty.pi? x)))))
(define llf.kind? (flat-named-contract 'llf.kind (λ (x) (or (llf.kind.pi? x)
                                                            (llf.kind.*? x)))))

(struct/contract llf.var ([n symbol?]) #:transparent)
(struct/contract llf.lam ([x symbol?] [T llf.ty?] [body llf.term?]) #:transparent)
(struct/contract llf.app ([t1 llf.term?] [t2 llf.term?]) #:transparent)

;; type variable/type family variable
(struct/contract llf.ty.var ([n symbol?]) #:transparent)
;; type family application
(struct/contract llf.ty.app ([T llf.ty?] [t llf.term?]) #:transparent)
;; Pi type
(struct/contract llf.ty.pi ([x symbol?][T llf.ty?][T1 llf.ty?]) #:transparent)

;; proper type kind
(struct/contract llf.kind.* () #:transparent)
;; type family kind
(struct/contract llf.kind.pi ([x symbol?] [T llf.ty?] [K llf.kind?]) #:transparent)

;; Parsers
(define-match-expander llf.Term
  (λ (stx)
    (syntax-case stx ()
      [(_ p) #`(app llf.term.parse p)])))

(define-match-expander llf.Ty
  (λ (stx)
    (syntax-case stx ()
      [(_ p) #`(app llf.ty.parse p)])))

(define-match-expander llf.Kind
  (λ (stx)
    (syntax-case stx ()
      [(_ p) #`(app llf.kind.parse p)])))

(define/contract (llf.term.parse sexp)
  (-> any/c llf.term?)
  (match sexp
    [(? symbol? n) (llf.var n)]
    [`(λ (,(? symbol? x) ,(llf.Ty T)) ,(llf.Term body)) (llf.lam x T body)]
    [`(,(llf.Term f) ,(llf.Term arg)) (llf.app f arg)]))

(define/contract (llf.ty.parse sexp)
  (-> any/c llf.ty?)
  (match sexp
    [(? symbol? n) (llf.ty.var n)]
    [`(,(llf.Ty f) ,(llf.Term arg)) (llf.ty.app f arg)]
    [`(π (,(? symbol? x) ,(llf.Ty T)) ,(llf.Ty T1)) (llf.ty.pi x T T1)]))

(define/contract (llf.kind.parse sexp)
  (-> any/c llf.kind?)
  (match sexp
    [`* (llf.kind.*)]
    [`(π (,(? symbol? x) ,(llf.Ty T)) ,(llf.Kind K)) (llf.kind.pi x T K)]))

;; Unparsers

(define/contract (llf.term.unparse term)
  (-> llf.term? any/c)
  (match term
    [(llf.var n) n]
    [(llf.lam x T body) `(λ [,x ,(llf.ty.unparse T)] ,(llf.term.unparse body))]
    [(llf.app f arg) `(,(llf.term.unparse f) ,(llf.term.unparse arg))]))

(define/contract (llf.ty.unparse ty)
  (-> llf.ty? any/c)
  (match ty
    [(llf.ty.var n) n]
    [(llf.ty.app f arg) `(,(llf.ty.unparse f) ,(llf.term.unparse arg))]
    [(llf.ty.pi x T T1) `(π [,x ,(llf.ty.unparse T)] ,(llf.ty.unparse T1))]))

(define/contract (llf.kind.unparse kind)
  (-> llf.kind? any/c)
  (match kind
    [(llf.kind.*) `*]
    [(llf.kind.pi x T K) `(π [,x ,(llf.ty.unparse T)] ,(llf.ty.unparse K))]))

;; substitutions for terms, types and kinds

(define/contract (llf.subst term x val)
  (-> llf.term? symbol? llf.term? llf.term?)
  (match term
    [(llf.var n) (if (eqv? x n)
                     val
                     term)]
    [(llf.app f arg) (llf.app (llf.subst f x val)
                              (llf.subst arg x val))]
    [(llf.lam x1 T body) (if (eqv? x x1)
                             term
                             (llf.lam x1 (llf.ty.subst T x val) (llf.subst body x val)))]))

(define/contract (llf.ty.subst ty x val)
  (-> llf.ty? symbol? llf.term? llf.ty?)
  (match ty
    [(llf.ty.var _) ty]
    [(llf.ty.app f arg) (llf.ty.app (llf.ty.subst f x val)
                                    (llf.subst arg x val))]
    [(llf.ty.pi x_ T T_) (llf.ty.pi x_ (llf.ty.subst T x val)
                                    (if (eqv? x x_)
                                        T_ (llf.ty.subst T_ x val)))]))

(define/contract (llf.kind.subst kind x val)
  (-> llf.kind? symbol? llf.term? llf.kind?)
  (match kind
    [(llf.kind.*) kind]
    [(llf.kind.pi x_ T K) (llf.kind.pi x_ (llf.ty.subst T x val)
                                       (if (eqv? x x_)
                                           K
                                           (llf.kind.subst K x val)))]))

;; term equivalences

(define/contract (llf.whnf term)
  (-> llf.term? llf.term?)
  (match term
    [(llf.var n) term]
    [(llf.lam x T body) term]
    [(llf.app (llf.lam x T body) arg) (llf.whnf (llf.subst body x arg))]
    [(llf.app f arg) (llf.app (llf.whnf f) arg)]))

;; term equivalence for terms
(define/contract (llf.term=? t1 t2)
  (-> llf.term? llf.term? boolean?)
  (define wt1 (llf.whnf t1))
  (define wt2 (llf.whnf t2))
  (llf.termw=? wt1 wt2))

;; term equivalence for weak head normal forms
(define/contract (llf.termw=? t1 t2)
  (-> llf.term? llf.term? boolean?)
  (match* (t1 t2)
    [((llf.var n1) (llf.var n2)) (eqv? n1 n2)]
    [((llf.lam x1 T1 body1) (llf.lam x2 T2 body2)) (define x3 (llf.var (gensym 'var)))
                                                   (llf.term=? (llf.subst body1 x1 x3)
                                                               (llf.subst body2 x2 x3))]
    [((llf.app f1 arg1) (llf.app f2 arg2)) (and (llf.termw=? f1 f2)
                                                (llf.termw=? arg1 arg2))]
    [((llf.lam x1 T1 body1) t2) ;; beta-equivalent
     (define fresh-x (llf.var (gensym 'var)))
     (llf.term=? (llf.subst body1 x1 fresh-x)
                 (llf.app t2 fresh-x))]
    [(t1 (llf.lam x2 T2 body2)) ;; symmetric case
     (llf.termw=? t2 t1)]
    [(_1 _2) #f]))

;; type equivalence

(define/contract (llf.ty=? ty1 ty2)
  (-> llf.ty? llf.ty? boolean?)
  (match* (ty1 ty2)
    [((llf.ty.var n1) (llf.ty.var n2)) (eqv? n1 n2)]
    [((llf.ty.app f1 arg1) (llf.ty.app f2 arg2)) (and (llf.ty=? f1 f2)
                                                      (llf.ty=? arg1 arg2))]
    [((llf.ty.pi x1 T1 T1_) (llf.ty.pi x2 T2 T2_))
     (define x3 (llf.var (gensym 'var)))
     (and (llf.ty=? T1 T2)
          (llf.ty=? (llf.ty.subst T1_ x1 x3)
                    (llf.ty.subst T2_ x2 x3)))]
    [(_1 _2) #f]))

;; kind equivalence

(define/contract (llf.kind=? kind1 kind2)
  (-> llf.kind? llf.kind? boolean?)
  (match* (kind1 kind2)
    [((llf.kind.*) (llf.kind.*)) #t]
    [((llf.kind.pi x1 T1 K1) (llf.kind.pi x2 T2 K2))
     (define x3 (llf.var (gensym 'var)))
     (and (llf.ty=? T1 T2)
          (llf.kind=? (llf.kind.subst K1 x1 x3)
                      (llf.kind.subst K2 x2 x3)))]
    [(_1 _2) #f]))

;; typing context
(define llf.ty.env? (hash/c symbol? llf.ty?))
(define/contract (llf.ty.env.ref env n)
  (-> llf.ty.env? symbol? llf.ty?)
  (hash-ref env n (λ () (error (format "type error: variable not found in typing context: ~a" n)))))

(define/contract (llf.ty.env.set env n ty)
  (-> llf.ty.env? symbol? llf.ty? llf.ty.env?)
  (hash-set env n ty))

;; kinding context
(define llf.kind.env? (hash/c symbol? llf.kind?))

(define/contract (llf.kind.env.ref env n)
  (-> llf.kind.env? symbol? llf.kind?)
  (hash-ref env n (λ () (error (format "type error: variable not found in kind context: ~a" n)))))

(define/contract (llf.typecheck term tenv kenv)
  (-> llf.term? llf.ty.env? llf.kind.env? llf.ty?)
  (define (tyck t) (llf.typecheck t tenv kenv))
  (match term
    [(llf.var n) (llf.ty.env.ref tenv n)]
    [(llf.lam x T body) (define T-kind (llf.kinding T tenv kenv))
                        (unless (llf.kind.*? T-kind) ;; check T :: * (kinding)
                          (error (format "type error: type ~a should have kind *, but got: ~a, in term: ~a"
                                         (llf.ty.unparse T) (llf.kind.unparse T-kind) (llf.term.unparse term))))
                        (llf.ty.pi x T (llf.typecheck body (llf.ty.env.set tenv x T) kenv))]
    [(llf.app f arg) (match* ((tyck f) (tyck arg))
                       [((llf.ty.pi x T1 T_) T2)
                        (unless (llf.ty=? T1 T2)
                          (error (format "type error: wrong argument type, expected: ~a, but got: ~a, in term: ~a"
                                         (llf.ty.unparse T1) (llf.ty.unparse T2)
                                         (llf.term.unparse term))))
                        (llf.ty.subst T_ x arg)]
                       [(ty1 ty2)
                        (error (format "type error: wrong function type, expected: pi, but got: ~a, in term: ~a"
                                       (llf.ty.unparse ty1)
                                       (llf.term.unparse term)))])]))

(define/contract (llf.kinding ty tenv kenv)
  (-> llf.ty? llf.ty.env? llf.kind.env? llf.kind?)
  (define (kinding ty) (llf.kinding ty tenv kenv))
  (match ty
    [(llf.ty.var n) (llf.kind.env.ref kenv n)]
    [(llf.ty.app f arg) (match* ((kinding f) (llf.typecheck arg tenv kenv))
                          [((llf.kind.pi x T1 K) T2)
                           (unless (llf.ty=? T1 T2)
                             (error (format "type error: wrong type family application arugment type, \
                       expected type: ~a, but got: ~a, in type: ~a"
                                            (llf.ty.unparse T1) (llf.ty.unparse T2) (llf.ty.unparse ty))))
                           (llf.kind.subst K x arg)]
                          [(kind1 ty2)
                           (error (format "kind error: type family application expect a pi kind, but got: ~a, in type: ~a"
                                          (llf.kind.unparse kind1) (llf.ty.unparse ty)))])]
    [(llf.ty.pi x T T_) (define T-kind (kinding T))
                        (unless (llf.kind.*? T-kind)
                          (error (format "kind error: variable of pi type should have * kind, but got: ~a, in type: ~a"
                                         (llf.kind.unparse T-kind) (llf.ty.unparse ty))))
                        (define T_-kind (llf.kinding T_ (llf.ty.env.set tenv x T) kenv))
                        (unless (llf.kind.*? T_-kind)
                          (error (format "kind error: return type of pi type should have * kind, but got: ~a, in type: ~a"
                                         (llf.kind.unparse T_-kind) (llf.ty.unparse ty))))
                        T_-kind]))

(define/contract (llf.tyck sexp)
  (-> any/c any/c)
  (llf.ty.unparse (llf.typecheck (llf.term.parse sexp) (hasheq) (hasheq))))


