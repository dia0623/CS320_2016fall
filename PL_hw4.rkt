#lang plai

(require (for-syntax racket/base) racket/match racket/list racket/string
         (only-in mzlib/string read-from-string-all))

;; build a regexp that matches restricted character expressions, can use only
;; {}s for lists, and limited strings that use '...' (normal racket escapes
;; like \n, and '' for a single ')
(define good-char "(?:[ \t\r\na-zA-Z0-9_{}!?*/<=>:+-]|[.][.][.])")
;; this would make it awkward for students to use \" for strings
;; (define good-string "\"[^\"\\]*(?:\\\\.[^\"\\]*)*\"")
(define good-string "[^\"\\']*(?:''[^\"\\']*)*")
(define expr-re
  (regexp (string-append "^"
                         good-char"*"
                         "(?:'"good-string"'"good-char"*)*"
                         "$")))
(define string-re
  (regexp (string-append "'("good-string")'")))

(define (string->sexpr str)
  (unless (string? str)
    (error 'string->sexpr "expects argument of type <string>"))
    (unless (regexp-match expr-re str)
      (error 'string->sexpr "syntax error (bad contents)"))
    (let ([sexprs (read-from-string-all
                 (regexp-replace*
                  "''" (regexp-replace* string-re str "\"\\1\"") "'"))])
    (if (= 1 (length sexprs))
      (car sexprs)
      (error 'string->sexpr "bad syntax (multiple expressions)"))))

(test/exn (string->sexpr 1) "expects argument of type <string>")
(test/exn (string->sexpr ".") "syntax error (bad contents)")
(test/exn (string->sexpr "{} {}") "bad syntax (multiple expressions)")

(define (symbol<? a b) (string<? (symbol->string a) (symbol->string b)))

;; type FunDef
(define-type FunDef
  [fundef (fun-name symbol?) (arg-name (listof symbol?)) (body FnWAE?)])

;; type Deferred Substitution
(define-type DefrdSub
  [mtSub]
  [aSub (name symbol?)
        (value (or/c rec? number?))
        (rest DefrdSub?)])

;; type Record
(define-type RECORD
  [record (name symbol?) (value FnWAE?)])

(define-type VALUE
  [numV (n number?)]
  [recV (r rec?)])

;; FnWAE abstract syntax trees
(define-type FnWAE
  [num (n number?)]
  [add (lhs FnWAE?) (rhs FnWAE?)]
  [sub (lhs FnWAE?) (rhs FnWAE?)]
  [with (name symbol?) (named-expr FnWAE?) (body FnWAE?)]
  [id (name symbol?)]
  [app (ftn symbol?) (arg (listof FnWAE?))]
  [rec (field (listof RECORD?))]
  [get (record FnWAE?) (id symbol?)])

; parse : sexp -> FnWAE
;; to convert s-expressions into FnWAEs
;; (parse (string->sexpr "{get {rec {r {+ 1 2}} {z {with {x 0} {f x}}}} z}")) should produce (get (rec (list (record 'r (add (num 1) (num 2))) (record 'z (with 'x (num 0) (app 'f (list (id 'x))))))) 'z)
;; (parse (string->sexpr "{get {rec {r 3}}}")) should produce "bad syntax"
(define (parse sexp)
  (match sexp
    [(? number?) (num sexp)]
    [(list '+ l r) (add (parse l) (parse r))]
    [(list '- l r) (sub (parse l) (parse r))]
    [(list 'with (list x i) b) (with x (parse i) (parse b))]
    [(? symbol?) (id sexp)] 
    [(list 'rec a ...) (if (= (length (remove-duplicates (map (lambda (r) (car r)) a)))
                              (length a))
                           (rec (map (lambda (r) (record (car r) (parse (cadr r)))) a))
                           (error 'parse "duplicate fields"))]
    [(list 'get r i) (get (parse r) i)] 
    [(list f x ...) (if (or (symbol=? f '+) (symbol=? f '-) (symbol=? f 'with) (symbol=? f 'rec) (symbol=? f 'get))
                        (error 'parse "bad syntax: ~a" sexp)
                        (app f (map parse x)))]
    ;[(list f a ...) (app f (map parse a))]
    [else (error 'parse "bad syntax: ~a" sexp)]))

(test (parse (string->sexpr "{get {rec {r {+ 1 2}} {z {with {x 0} {f x}}}} z}"))(get (rec (list (record 'r (add (num 1) (num 2))) (record 'z (with 'x (num 0) (app 'f (list (id 'x))))))) 'z))
(test/exn (parse (string->sexpr "{get {rec {r 3}}}")) "bad syntax")

; parse-string : string -> FnWAE
;; parses a string containing a FnWAE expression to a FnWAE AST
;;(parse-string "{get {rec {r {+ 1 2}} {z {with {x 0} {f x}}}} z}")) should produce (get (rec (list (record 'r (add (num 1) (num 2))) (record 'z (with 'x (num 0) (app 'f (list (id 'x))))))) 'z)
(define (parse-string str)
  (parse (string->sexpr str)))

(test (parse-string "{get {rec {r {+ 1 2}} {z {with {x 0} {f x}}}} z}") (get (rec (list (record 'r (add (num 1) (num 2))) (record 'z (with 'x (num 0) (app 'f (list (id 'x))))))) 'z))

; uniq?: list-of-symbol -> bool
;; check if every element in the list is unique
;; test (uniq? '()) should produce #t
;; test (uniq? '(x)) should produce #t
;; test (uniq? '(x y z)) should produce #t
;; test (uniq? '(z x y x)) should produce #f
(define (uniq? lst)
  (local [(define sorted-lst (sort lst symbol<?))]
    (define (uniq?-iter l)
      (cond [(null? l) #t]
            [(null? (cdr l)) #t]
            [(symbol=? (car l) (cadr l)) #f]
            [else (uniq?-iter (cdr l))]))
    (uniq?-iter sorted-lst)))

(test (uniq? '()) #t)
(test (uniq? '(x)) #t)
(test (uniq? '(x y z)) #t)
(test (uniq? '(z x y x)) #f)

; parse-defn : sexp -> FunDef
;; convert s-expression to FunDef
;;(parse-defn '(deffun (f x y z) (- x (+ y z)))) should be (fundef 'f '(x y z) (sub (id 'x) (add (id 'y) (id 'z))))
;;(parse-defn '(deffun (f x y x) (+  x y))) should be "bad syntax"
(define (parse-defn sexp)
  (match sexp
    [(list 'deffun (list f x ...) body)
     (unless (uniq? x)
       (error 'parse-defn "bad syntax"))
     (fundef f x (parse body))]))

(test (parse-defn '(deffun (f x y z) (- x (+ y z)))) (fundef 'f '(x y z) (sub (id 'x) (add (id 'y) (id 'z)))))
(test/exn (parse-defn '(deffun (f x y x) (+  x y))) "bad syntax")

; lookup-fundef : symbol list-of-FunDef -> FunDef
;; find a function in a list of fundef and return the function
;;(lookup-fundef 'g (list (parse-defn '{deffun {f} 4}) (parse-defn '{deffun {g x} {+ x x}}))) should produce (fundef 'g '(x) (add (id 'x) (id 'x)))
;;(lookup-fundef 'h (list (parse-defn '{deffun {f} 4}) (parse-defn '{deffun {g x} {+ x x}}))) should produce "unknown function"
(define (lookup-fundef name fundefs)
  (if (empty? fundefs)
      (error 'lookup-fundef "unknown function")
      (if (symbol=? name (fundef-fun-name (first fundefs)))
          (first fundefs)
          (lookup-fundef name (rest fundefs)))))

(test (lookup-fundef 'g (list (parse-defn '{deffun {f} 4}) (parse-defn '{deffun {g x} {+ x x}}))) (fundef 'g '(x) (add (id 'x) (id 'x))))
(test/exn (lookup-fundef 'h (list (parse-defn '{deffun {f} 4}) (parse-defn '{deffun {g x} {+ x x}}))) "unknown function")

; lookup : symbol DefrdSub -> number
;; to find the value of a symbol in a Deferred Substitution list
;;(lookup 'y (aSub 'x 1 (aSub 'y 2 (mtSub)))) should produce (numV 2)
;;(lookup 'z (aSub 'x 1 (aSub 'y 2 (mtSub)))) should produce "free variable"
(define (lookup name ds)
  (type-case DefrdSub ds
    [mtSub () (error 'lookup "free variable")]
    [aSub (x val rest)
          (if (symbol=? x name)
              (if (number? val) (numV val) (recV val))
              (lookup name rest))]))

(test (lookup 'y (aSub 'x 1 (aSub 'y 2 (mtSub)))) (numV 2))
(test/exn (lookup 'z (aSub 'x 1 (aSub 'y 2 (mtSub)))) "free variable")

; lookup-record : symbol list-of-RECORD -> FnWAE
;; find the value of record in a list of RECORDs
;;(lookup-record 'x (list (record 'x (num 0)))) should produce (num 0)
;;(lookup-record 'y (list (record 'x (num 0)))) should produce "no such field"
(define (lookup-record name record)
  (if (empty? record)
      (error 'lookup-record "no such field")
      (if (symbol=? name (record-name (car record)))
          (record-value (car record))
          (lookup-record name (cdr record)))))

(test (lookup-record 'x (list (record 'x (num 0)))) (num 0))
(test/exn (lookup-record 'y (list (record 'x (num 0)))) "no such field")

; interp : FnWAE list-of-FunDef -> VALUE
;; evaluate FnWAE expression to a value(num or record)
;;(interp (parse-string "{get {rec {a {f 1}} {b {- 1 2}}} b}") (list (parse-defn '{deffun {f a} {with {x 5} {+ x a}}})) (mtSub)) should produce (numV -1)
;;(interp (parse-string "{f 1 2 3}") (list (parse-defn '{deffun {f a b} {+ a b}})) (mtSub)) should produce "wrong arity"
(define (interp fnwae fundefs ds)
  (type-case FnWAE fnwae
    [num (n) (numV n)]
    [add (l r) (numV (+ (numV-n (interp l fundefs ds)) (numV-n (interp r fundefs ds))))]
    [sub (l r) (numV (- (numV-n (interp l fundefs ds)) (numV-n (interp r fundefs ds))))]
    ;[with (x i b) (interp b fundefs (aSub x (interp i fundefs ds) ds))]
    [with (x i b) (interp b fundefs (aSub x
                                          (local [(define v (interp i fundefs ds))]
                                            (if (numV? v) (numV-n v) (recV-r v)))
                                          ds))]
    [id (s) (lookup s ds)]
    [app (f a) (local [(define a-fundef (lookup-fundef f fundefs))]
                 (if (not (= (length a) (length (fundef-arg-name a-fundef))))
                     (error 'interp "wrong arity")
                     (interp (fundef-body a-fundef)
                         fundefs
                         (foldr aSub (mtSub)
                                (fundef-arg-name a-fundef)
                                (map (lambda (v) (if (numV? (interp v fundefs ds))
                                                     (numV-n (interp v fundefs ds))
                                                     (recV-r (interp v fundefs ds))))
                                     a)))))]
    [rec (l) (recV (rec (map (lambda (r) (record (record-name r)
                                                 (local [(define val (interp (record-value r) fundefs ds))]
                                                   (if (numV? val) (num (numV-n val)) (recV-r val)))))
                             l)))]
    [get (r i) (interp (lookup-record i (rec-field (recV-r (interp r fundefs ds))))
                       fundefs
                       ds)]))

(test (interp (parse-string "{get {rec {a {f 1}} {b {- 1 2}}} b}") (list (parse-defn '{deffun {f a} {with {x 5} {+ x a}}})) (mtSub)) (numV -1))
(test/exn (interp (parse-string "{f 1 2 3}") (list (parse-defn '{deffun {f a b} {+ a b}})) (mtSub)) "wrong arity")

; interp-expr : VALUE -> num or string
;; returns number if interpV is numV, 'record if interpV is recV
;;(interp-expr (numV 3)) should produce 3
;;(interp-expr (recV (rec (list (record 'x (num 3)))))) should produce 'record
(define (interp-expr interpV)
  (if (numV? interpV) (numV-n interpV) 'record))

(test (interp-expr (numV 3)) 3)
(test (interp-expr (recV (rec (list (record 'x (num 3)))))) 'record)

;; evaluate a FnWAE program contained in a string
(define (run str fundefs)
  (interp-expr (interp (parse-string str) fundefs (mtSub))))

;; test
(test (run "{f 1 2}" (list (parse-defn '{deffun {f x y} {+ x y}}))) 3)
(test (run "{+ {f} {f}}" (list (parse-defn '{deffun {f} 5}))) 10)
(test/exn (run "{f 1}" (list (parse-defn '{deffun {f x y} {+ x y}})))
          "wrong arity")

(test (run "{rec {a 10} {b {+ 1 2}}}" empty)
      'record)
(test (run "{get {rec {a 10} {b {+ 1 2}}} b}" empty)
      3)
(test/exn (run "{get {rec {b 10} {b {+ 1 2}}} b}" empty)
          "duplicate fields")
(test/exn (run "{get {rec {a 10}} b}" empty)
          "no such field")
(test (run "{g {rec {a 0} {c 12} {b 7}}}"
           (list (parse-defn '{deffun {g r} {get r c}})))
      12)
(test (run "{get {rec {r {rec {z 0}}}} r}" empty)
      'record)
(test (run "{get {get {rec {r {rec {z 0}}}} r} z}" empty)
      0)
(test/exn (run "{rec {z {get {rec {z 0}} y}}}" empty)
          "no such field")
(test (run "{with {x {f 2 5}} {g x}}" (list (parse-defn '{deffun {f a b} {+ a b}}) (parse-defn '{deffun {g x} {- x 5}}))) 2)
(test (run "{f 1 2}" (list (parse-defn '{deffun {f x y} {+ x y}}))) 3)
(test (run "{+ {f} {f}}" (list (parse-defn '{deffun {f} 5}))) 10)
(test (run "{h 1 4 5 6}" (list (parse-defn '{deffun {h x y z w} {+ x w}}) (parse-defn '{deffun {g x y z w} {+ y z}}))) 7)
(test (run "{with {x 10} {- {+ x {f}} {g 4}}}" (list (parse-defn '{deffun {f} 4}) (parse-defn '{deffun {g x} {+ x x}}))) 6)

(test (run "{rec {a 10} {b {+ 1 2}}}" empty) 'record)
(test (run "{get {rec {a 10} {b {+ 1 2}}} b}" empty) 3)
(test (run "{g {rec {a 0} {c 12} {b 7}}}" (list (parse-defn '{deffun {g r} {get r c}}))) 12)
(test (run "{get {rec {r {rec {z 0}}}} r}" empty) 'record)
(test (run "{get {get {rec {r {rec {z 0}}}} r} z}" empty) 0)
(test (run "{with {x 3} {with {y 5} {get {rec {a x} {b y}} a}}}" empty) 3)
(test (run "{with {x {f {rec {a 10} {b 5}} 2}} {g x}}" (list (parse-defn '{deffun {f a b} {+ {get a a} b}}) (parse-defn '{deffun {g x} {+ 5 x}}))) 17)
(test (run "{get {f 1 2 3 4 5} c}" (list (parse-defn '{deffun {f a b c d e} {rec {a a} {b b} {c c} {d d} {e e}}}))) 3)
(test (run "{get {f 1 2 3} b}" (list (parse-defn '{deffun {f a b c} {rec {a a} {b b} {c c}}}))) 2)
(test (run "{get {f 1 2 3} y}" (list (parse-defn '{deffun {f a b c} {rec {x a} {y b} {z c} {d 2} {e 3}}}))) 2)
(test (run "{get {f 1 2 3} d}" (list (parse-defn '{deffun {f a b c} {rec {x a} {y b} {z c} {d 2} {e 3}}}))) 2)
(test (run "{f {get {get {rec {a {rec {a 10} {b {- 5 2}}}} {b {get {rec {x 50}} x}}} a} b}}" (list (parse-defn '{deffun {f x} {+ 5 x}}))) 8)
(test (run "{get {rec {a 10} {b {+ 1 2}}} b}" empty) 3)
(test (run "{g {rec {a 0} {c 12} {b 7}}}" (list (parse-defn '{deffun {g r} {get r c}}))) 12)
(test (run "{get {rec {r {rec {z 0}}}} r}" empty) 'record)
(test (run "{get {get {rec {r {rec {z 0}}}} r} z}" empty) 0)
(test (run "{rec {a 10}}" empty) `record)
(test (run "{get {rec {a 10}} a}" empty) 10)
(test (run "{get {rec {a {+ 1 2}}} a}" empty) 3)
(test (run "{rec }" empty) `record)
(test (run "{get {rec {a {rec {b 10}}}} a}" empty) `record)
(test (run "{get {get {rec {a {rec {a 10}}}} a} a}" empty) 10)
(test (run "{get {get {rec {a {rec {a 10} {b 20}}}} a} a}" empty) 10)
(test (run "{get {get {rec {a {rec {a 10} {b 20}}}} a} b}" empty) 20)
(test (run "{+ {get {rec {a 10}} a} {get {rec {a 20}} a}}" empty) 30)
(test (run "{+ {get {rec {a 10}} a} {get {rec {a 20}} a}}" empty) 30)
(test (run "{rec {a 10}}" empty) `record)
(test (run "{rec {a {- 2 1}}}" empty) `record)
(test (run "{get {rec {a 10}} a}" empty) 10)
(test (run "{get {rec {a {- 2 1}}} a}" empty) 1)
(test (run "{get {rec {a {rec {b 10}}}} a}" empty) `record)
(test (run "{get {get {rec {a {rec {a 10}}}} a} a}" empty) 10)
(test (run "{get {get {rec {a {rec {a 10} {b 20}}}} a} a}" empty) 10)
(test (run "{get {get {rec {a {rec {a 10} {b 20}}}} a} b}" empty) 20)
(test (run "{rec {a 10} {b {+ 1 2}}}" empty) 'record)
(test (run "{get {rec {a 10} {b {+ 1 2}}} b}" empty) 3)
(test (run "{get {rec {r {rec {z 0}}}} r}" empty) 'record)
(test (run "{get {get {rec {r {rec {z 0}}}} r} z}" empty) 0)
(test (run "{rec {a 10} {b {+ 1 2}}}" empty) 'record)
(test (run "{get {rec {a 10} {b {+ 1 2}}} b}" empty) 3)
(test (run "{g {rec {a 0} {c 12} {b 7}}}" (list (parse-defn '{deffun {g r} {get r c}}))) 12)
(test (run "{get {rec {r {rec {z 0}}}} r}" empty) 'record)
(test (run "{get {get {rec {r {rec {z 0}}}} r} z}" empty) 0)
(test (run "{with {y {rec {x 1} {y 2} {z 3}}} {get y y}}" empty) 2)
(test (run "{with {y {rec {x 1} {y 2} {z 3}}} {get y z}}" empty) 3)
(test (run "{rec {a 10} {b {+ 1 2}}}" empty) 'record)
(test (run "{get {rec {a 10} {b {+ 1 2}}} b}" empty) 3)
(test (run "{g {rec {a 0} {c 12} {b 7}}}" (list (parse-defn '{deffun {g r} {get r c}}))) 12)
(test (run "{get {rec {r {rec {z 0}}}} r}" empty) 'record)
(test (run "{get {get {rec {r {rec {z 0}}}} r} z}" empty) 0)