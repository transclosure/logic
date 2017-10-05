#lang racket

(require "base1.rkt")
(require redex)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define test1 (term (() (alloc 5))))
(apply-reduction-relation* eval-lambdaJS-errors test1)
(define test2 (term (() (if #f (alloc 100) (alloc 200)))))
(apply-reduction-relation* eval-lambdaJS-errors test2)
(define test3 (term (() (begin (alloc 11) (alloc 12) 10))))
(apply-reduction-relation* eval-lambdaJS-errors test3)

(define test4 (term (((123 undefined)) (set! (ref 123) (err 10)))))
(apply-reduction-relation* eval-lambdaJS-errors test4)
(define test5 (term (((123 undefined)) (set! (ref 123) 0))))
(apply-reduction-relation* eval-lambdaJS-errors test5)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Note diff here: have to include errors
(define (value-or-error? t) (or (redex-match? lambdaJS val t)
                                (redex-match? lambdaJS error t)))
(define (reduces? t) (not (empty? (apply-reduction-relation eval-lambdaJS-errors t))))
(define (annoying? t) (or (redex-match? lambdaJS variable-not-otherwise-mentioned t)))

; base 5 log by default (bound on how big the generated terms can get as func of how many have been generated so far)
; NOTE: likely to want this to grow faster if suspect larger terms cause a problem
(define my-attempt-size default-attempt-size)

(redex-check lambdaJS e (or (value-or-error? (term e))
                            (reduces? (term (() e)))
                            (annoying? (term e)))
             #:prepare (lambda (t)
                         (begin (printf "checking: ~a~n" t)
                                t))
             #:attempts 10000
             ; Print the output (don't raise an exception).
             ; Note that this does NOT print every term tested, which is what the above #:prepare function does.
             #:print? #t
             #:attempt-size my-attempt-size)
