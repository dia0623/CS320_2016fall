#lang plai

(define-type FAE-Value
  [numV (n number?)]
  [closureV (param symbol?) (body FAE?) (ds DefrdSub?)])

(define-type DefrdSub
  [mtSub]
  [aSub (name symbol?) (value FAE-Value?) (rest DefrdSub?)])

(define-type FAE
  [num (n number?)]
  [add (lhs FAE?) (rhs FAE?)]
  [sub (lhs FAE?) (rhs FAE?)]
  [with (name symbol?) (named-expr FAE?) (body FAE?)]
  [id (s symbol?)]
  [fun (param symbol?) (body FAE?)]
  [app (ftn FAE?) (arg FAE?)])

(define (num+ x y)
  (numV (+ (numV-n x) (numV-n y))))
(define (num- x y)
  (numV (- (numV-n x) (numV-n y))))

(define (lookup s ds)
  (if (mtSub? ds) (error 'lookup "no such id")
      (if (symbol=? s (aSub-name ds)) (aSub-value ds)
          (lookup s (aSub-rest ds)))))

(define (interp fae ds)
  (type-case FAE fae
    [num (n) (numV n)]
    [add (l r) (num+ (interp l ds) (interp r ds))]
    [sub (l r) (num- (interp l ds) (interp r ds))]
    [with (x i b) (interp b (aSub x (interp i ds) ds))]
    [id (s) (lookup s ds)]
    [fun (x b) (closureV x b ds)]
    [app (f a) (local [(define f-val (interp f ds))
                       (define a-val (interp a ds))]
                 (interp (closureV-body f-val)
                         (aSub (closureV-param f-val)
                               a-val
                               (closureV-ds f-val))))]))