#lang plai

(define (f)
  (do-f 0))

(define (web-read/k prompt cont)
  (local [(define key (remember cont))]
    `(,prompt "To continue, call resume/k with " ,key "and value")))

(define (resume/k key val)
  (local [(define cont (lookup key))]
    (cont val)))

(define (do-f total)
  (web-read/k
   (format "Total is ~a\nNext number...\n" total)
   (lambda (val)
     (do-f (+ total val)))))

(define table empty)

(define (remember v)
  (local [(define n (length table))]
    (begin
      (set! table (append table (list v)))
      n)))

(define (lookup key)
  (list-ref table key))

(define (do-g cont)
  (web-read/k "First number"
              (lambda (v1)
                (web-read/k "Second number"
                            (lambda (v2)
                              (cont (+ v1 v2)))))))

(define (g)
  (do-g identity))

(define (web-read prompt)
  (let/cc cont
    (local [(define key (remember cont))]
      (error 'web-read
             "~a; to continue, call resume with ~a and value"
             prompt key))))

(define (g2)
  (+ (web-read "First")
     (web-read "Second")))