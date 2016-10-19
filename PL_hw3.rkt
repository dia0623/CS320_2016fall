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

;; PWAE abstract syntax trees
(define-type PWAE
  [num  (num (listof number?))]
  [add  (left PWAE?) (right PWAE?)]
  [sub  (left PWAE?) (right PWAE?)]
  [with (name symbol?) (init PWAE?) (body PWAE?)]
  [id   (name symbol?)]
  [pooh (exp (listof PWAE?)) (op symbol?)])

;rmv-last : list -> list
;; remove last element of the list
;; (rmv-last '(1 2 3)) should return '(1 2)
;; (rmv-last '()) should return '()
(define (rmv-last lst)
  (cond ((null? lst) '())
        ((null? (cdr lst)) '())
        (else (cons (car lst)
                    (rmv-last (cdr lst))))))

(test (rmv-last '(1 2 3)) '(1 2))
(test (rmv-last '()) '())

; parse-sexpr : sexpr -> PWAE
;; to convert s-expressions into PWAEs
;; (parse-sexpr (string->sexpr "{with {x {pooh 3 4 -}} {pooh {+ {pooh 1 2 -} 5} x +}}")) should produce 
;; (with 'x (pooh (list (num '(3)) (num '(4))) '-) (pooh (list (add (pooh (list (num '(1)) (num '(2))) '-) (num '(5))) (id 'x)) '+))
;; (parse-sexpr (string->sexpr "{with {x {pooh 1 2 3 -} {- 3 4 5}}}") should produce "bad syntax: ~a"
(define (parse-sexpr sexp)
  (define (is_pooh? sexp)
    (and (symbol=? 'pooh (car sexp))
         (symbol? (last sexp))))
  (define (parse-pooh exp)
    (if (null? exp)
        '()
        (cons (parse-sexpr (car exp))
              (parse-pooh (cdr exp)))))
  (match sexp
    [(? number?) (num (list sexp))]
    [(? (listof number?)) (num sexp)]
    [(list '+ l r) (add (parse-sexpr l) (parse-sexpr r))]
    [(list '- l r) (sub (parse-sexpr l) (parse-sexpr r))]
    [(list 'with (list x i) b) (with x (parse-sexpr i) (parse-sexpr b))]
    [(? symbol?) (id sexp)]
    [(? is_pooh?) (pooh (parse-pooh (rmv-last (cdr sexp))) (last sexp))]
    [else (error 'parse "bad syntax: ~a" sexp)]))

(test (parse-sexpr (string->sexpr "{with {x {pooh 3 4 -}} {pooh {+ {pooh 1 2 -} 5} x +}}")) (with 'x (pooh (list (num '(3)) (num '(4))) '-) (pooh (list (add (pooh (list (num '(1)) (num '(2))) '-) (num '(5))) (id 'x)) '+)))
(test/exn (parse-sexpr (string->sexpr "{with {x {pooh 1 2 3 -} {- 3 4 5}}}")) "parse: bad syntax: (with (x (pooh 1 2 3 -) (- 3 4 5)))")

;; parses a string containing a PWAE expression to a PWAE AST
(define (parse str)
  (parse-sexpr (string->sexpr str)))

;; substitutes the second argument with the third argument in the
;; first argument, as per the rules of substitution; the resulting
;; expression contains no free instances of the second argument
;; (subst (string->sexpr "{with {x {with {x 20} {+ z x}}} {with {y 10} {pooh x y -}}}")) 'z '(10)) should produce
;; (with 'x (with 'x (num '(20)) (add (num '(10)) (id 'x))) (with 'y (num '(10)) (pooh (list (id 'x) (id 'y)) '-)))
(define (subst expr from to)
  (define (subst-pooh lst from to)
    (if (null? lst)
        '()
        (cons (subst (car lst) from to) (subst-pooh (cdr lst) from to))))
  (type-case PWAE expr
    [num (n)   expr]
    [add (l r) (add (subst l from to) (subst r from to))]
    [sub (l r) (sub (subst l from to) (subst r from to))]
    [id (name) (if (symbol=? name from) (num to) expr)]
    [with (bound-id named-expr bound-body)
          (with bound-id
                (subst named-expr from to)
                (if (symbol=? bound-id from)
                    bound-body
                    (subst bound-body from to)))]
    [pooh (lst op) (pooh (subst-pooh lst from to) op)]))

(test (subst (parse-sexpr (string->sexpr "{with {x {with {x 20} {+ z x}}} {with {y 10} {pooh x y -}}}")) 'z '(10))(with 'x (with 'x (num '(20)) (add (num '(10)) (id 'x))) (with 'y (num '(10)) (pooh (list (id 'x) (id 'y)) '-))))

;bin-op : (number number -> number) (listof number or number) (listof number or number) -> (listof number))
;; applies a binary numeric function on all combinations of numbers from
;; the two input lists or numbers, and return the list of all of the results
(define (bin-op op ls rs)
  (define (helper l rs)
    ;; f : number -> number
    (define (f n)
      (op l n))
    (map f rs))
  (if (null? ls)
    null
    (append (helper (first ls) rs) (bin-op op (rest ls) rs))))

;; evaluates PWAE expressions by reducing them to numbers
;; (eval (parse "{with {x {pooh 3 4 -}} {pooh {+ {pooh 1 2 -} 5} x +}}")) should produce '(3)
(define (eval expr)
  (define (eval-pooh op lst)
    (if (null? (cddr lst))
        (bin-op op (eval (car lst)) (eval (last lst)))
        (bin-op op (eval-pooh op (rmv-last lst)) (eval (last lst)))))
  (type-case PWAE expr
    [num (n) n]
    [add (l r) (bin-op + (eval l) (eval r))]
    [sub (l r) (bin-op - (eval l) (eval r))]
    [with (bound-id named-expr bound-body)
          (eval (subst bound-body
                       bound-id
                       (eval named-expr)))]
    [id (name) (error 'eval "free identifier: ~s" name)]
    [pooh (lst op) (if (symbol=? op '+)
                       (eval-pooh + lst)
                       (eval-pooh - lst))]))

(test (eval (parse "{with {x {pooh 3 4 -}} {pooh {+ {pooh 1 2 -} 5} x +}}")) '(3))

; run : string -> listof number
;; evaluate a PWAE program contained in a string
(define (run str)
  (eval (parse str)))

;; tests
(test (run "5") '(5))
(test (run "{+ 5 5}") '(10))
(test (run "{with {x {+ 5 5}} {+ x x}}") '(20))
(test (run "{with {x 5} {+ x x}}") '(10))
(test (run "{with {x {+ 5 5}} {with {y {- x 3}} {+ y y}}}") '(14))
(test (run "{with {x 5} {with {y {- x 3}} {+ y y}}}") '(4))
(test (run "{with {x 5} {+ x {with {x 3} 10}}}") '(15))
(test (run "{with {x 5} {+ x {with {x 3} x}}}") '(8))
(test (run "{with {x 5} {+ x {with {y 3} x}}}") '(10))
(test (run "{with {x 5} {with {y x} y}}") '(5))
(test (run "{with {x 5} {with {x x} x}}") '(5))
(test/exn (run "{with {x 1} y}") "free identifier")

(test (run "{+ {2 1} {3 4}}") '(5 6 4 5))
(test (run "{+ {- {+ 1 3} 2} {10 -10}}") '(12 -8))

(test (run "{+ 3 7}") '(10))
(test (run "{- 10 {3 5}}") '(7 5))
(test (run "{with {x {+ 5 5}} {+ x x}}") '(20))

(test (run "{+ {+ {pooh 1 2 -} 5} {pooh 3 4 -}}") '(3))
(test (run "{pooh {+ {pooh 1 2 -} 5} {- 3 4} +}") '(3))
(test (run "{pooh {pooh {pooh 1 2 -} 5 +} {pooh 3 4 -} +}") '(3))
(test (run "{+ {+ {- 1 2} 5} {- 3 4}}") '(3))
(test (run "{with {x {pooh 3 4 -}} {pooh {+ {pooh 1 2 -} 5} x +}}") '(3))

(test (run "{+ {+ {pooh 1 2 -} 5} {pooh 3 4 -}}") '(3))
(test (run "{pooh {+ {pooh 1 2 -} 5} {- 3 4} +}") '(3))
(test (run "{pooh {pooh {pooh 1 2 -} 5 +} {pooh 3 4 -} +}") '(3))
(test (run "{+ {+ {- 1 2} 5} {- 3 4}}") '(3))
(test (run "{with {x {pooh 3 4 -}} {pooh {+ {pooh 1 2 -} 5} x +}}") '(3))
(test (run "{pooh 1 2 -}") '(-1))
(test (run "{+ {+ {pooh 1 2 -} 5} {pooh 3 4 -}}") '(3))
(test (run "{pooh {+ {pooh 1 2 -} 5} {- 3 4} +}") '(3))
(test (run "{pooh {pooh {pooh 1 2 -} 5 +} {pooh 3 4 -} +}") '(3))
(test (run "{+ {+ {- 1 2} 5} {- 3 4}}") '(3))
(test (run "{with {x {pooh 3 4 -}} {pooh {+ {pooh 1 2 -} 5} x +}}") '(3))
(test (run "{with {x {with {x 20} {pooh 1 x +}}} {with {y 10} {pooh x y -}}}") '(11))
(test (run "{with {x {pooh 1 2 3 4 5 +}} x}") '(15))
(test (run "{pooh {with {x {pooh {1 2} {3 4} 1 +}} x} 2 3 -}") '(0 1 1 2))
(test (run "{pooh 1 2 3 4 5 +}") '(15))
(test (run "{pooh {1 2 3} {4 5} -}") '(-3 -4 -2 -3 -1 -2))
(test (run "{+ {+ {pooh 1 2 -} 5} {pooh 3 4 -}}") '(3))
(test (run "{pooh {+ {pooh 1 2 -} 5} {- 3 4} +}") '(3))
(test (run "{pooh {pooh {pooh 1 2 -} 5 +} {pooh 3 4 -} +}") '(3))
(test (run "{+ {+ {- 1 2} 5} {- 3 4}}") '(3))
(test (run "{with {x {pooh 3 4 -}} {pooh {+ {pooh 1 2 -} 5} x +}}") '(3))
(test (run "{pooh 1 2 3 4 +}") '(10))
(test (run "{pooh {3 4} {-4 0} 5 +}") '(4 8 5 9))
(test (run "{pooh 1 2 3 4 -}") '(-8))
(test (run "{pooh {4 1} 1 {5 6 7} -}") '(-2 -3 -4 -5 -6 -7))
(test (run "{+ {pooh 1 {4 9} -3 {2 0 1} +} {- {pooh {3 4} {2} -} 4}}") '(1 2 -1 0 0 1 6 7 4 5 5 6))
(test (run "{pooh 1 {pooh 1 2 -} 3 +}") '(3))
(test (run "{+ {+ {pooh 1 2 -} 5} {pooh 3 4 -}}") '(3))
(test (run "{pooh {+ {pooh 1 2 -} 5} {- 3 4} +}") '(3))
(test (run "{pooh {pooh {pooh 1 2 -} 5 +} {pooh 3 4 -} +}") '(3))
(test (run "{+ {+ {- 1 2} 5} {- 3 4}}") '(3))
(test (run "{with {x {pooh 3 4 -}} {pooh {+ {pooh 1 2 -} 5} x +}}") '(3))
(test (run "{pooh {2 1} {3 4} +}") '(5 6 4 5))
(test (run "{with {x {1 2}} {pooh x {+ {1 2} 1} -}}") '(-1 -2 0 -1))
(test (run "{with {x {1 2}} {pooh x {pooh {1 2} 1 +} -}}") '(-1 -2 0 -1))
(test (run "{+ {+ {pooh 1 2 -} 5} {pooh 3 4 -}}") '(3))
(test (run "{pooh {+ {pooh 1 2 -} 5} {- 3 4} +}") '(3))
(test (run "{pooh {pooh {pooh 1 2 -} 5 +} {pooh 3 4 -} +}") '(3))
(test (run "{+ {+ {- 1 2} 5} {- 3 4}}") '(3))
(test (run "{with {x {pooh 3 4 -}} {pooh {+ {pooh 1 2 -} 5} x +}}") '(3))
(test (run "{with {x {with {y {1 -2}} {pooh 1 y 2 -}}} {+ x x}}") '(-4 -1 -1 2))
(test (run "{pooh {0 1} {2 3} {4 5} 6 +}") '(12 13 13 14 13 14 14 15))
(test (run "{with {x {pooh 8 7 -}} {with {x 10} {+ x 3}}}") '(13))
(test (run "{pooh {pooh 1 2 {2 3} {1 2} -} {2 1 3 2} {1 2} +}") '(-1 0 -2 -1 0 1 -1 0 -2 -1 -3 -2 -1 0 -2 -1 -2 -1 -3 -2 -1 0 -2 -1 -3 -2 -4 -3 -2 -1 -3 -2))
(test (run "{with {x {pooh {1 2} {2 3} 1 +}} {pooh x 1 2 +}}") '(7 8 8 9))
(test (run "{with {x {pooh 3 4 -}} {pooh {+ {pooh 1 2 -} 5} x +}}") '(3))
(test (run "{with {x {with {x 20} {pooh 1 x +}}} {with {y 10} {pooh x y -}}}") '(11))
(test (run "{with {x {pooh 1 2 3 4 5 +}} x}") '(15))
(test (run "{pooh {with {x {pooh {1 2} {3 4} 1 +}} x} 2 3 -}") '(0 1 1 2))
(test (run "{pooh {1 2 3} {4 5} -}") '(-3 -4 -2 -3 -1 -2))