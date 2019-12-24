#lang rosette/safe

(require "base1.rkt")
(require redex)
(require rosette/lib/angelic)

#|
Direct Tests
|#
(define (run-test t) (apply-reduction-relation* eval-lambdaJS-errors t))
(define test1 (term (() (alloc 5))))
(define test2 (term (() (if #f (alloc 100) (alloc 200)))))
(define test3 (term (() (begin (alloc 11) (alloc 12) 10))))
(define test4 (term (((123 undefined)) (set! (ref 123) (err 10)))))
(define test5 (term (((123 undefined)) (set! (ref 123) 0))))

#|
Redex Checking
|#
; Note diff here: have to include errors
(define (value-or-error? t) (or (redex-match? lambdaJS val t)
                                (redex-match? lambdaJS error t)))
(define (reduces? t) (not (empty? (apply-reduction-relation eval-lambdaJS-errors t))))
(define (annoying? t) (or (redex-match? lambdaJS variable-not-otherwise-mentioned t)))

; base 5 log by default (bound on how big the generated terms can get,
; as func of how many have been generated so far)
; NOTE: likely to want this to grow faster if suspect larger terms cause a problem
(define my-attempt-size default-attempt-size)

(define (check1) (redex-check lambdaJS e (or (value-or-error? (term e))
                                             (reduces? (term (() e)))
                                             (annoying? (term e)))
                              #:prepare (lambda (t)
                                          (begin (printf "checking: ~a~n" t)
                                                 t))
                              #:attempts 10000
                              ; Print the output (don't raise an exception).
                              ; Note that this does NOT print every term tested,
                              ; which is what the above #:prepare function does.
                              #:print? #t
                              #:attempt-size my-attempt-size))

#|
The following is a *program* that produces all possible terms, with a simple property
|#

;;(loc natural) ; a heap location
(define (a-loc)
  (define-symbolic* loc integer?)
  (assert (or (zero? loc) (positive? loc)))
  (term ,loc))
  
;;(prim number #t #f undefined null) ; primitives: nums, AVOIDING strs, bools, undef, null
(define (a-number)
  (define-symbolic* num real?) ; AVOIDING unreal numbers
  (term ,num))
(define (the-undefined)
  (term undefined))
(define (the-null)
  (term null))
(define (the-true)
  (term true))
(define (the-false)
  (term false))
(define (a-prim)
  (term, (choose* (a-number) (the-true) (the-false) (the-undefined) (the-null))))
  
;;(val prim (ref loc)) ; a value is a primitive or a heap reference
(define (a-val)
  (term ,(choose* (a-prim) `(ref ,(a-loc)))))

;;(σ ((loc val) ...)) ; a heap
(define (a-loc.val)
  (term (,(a-loc) ,(a-val))))
(define (a-σ)
  (define-symbolic* k integer?)
  (define σ (take (list (a-loc.val)
                        (a-loc.val)
                        (a-loc.val))
                  k))
  (assert (and (>= k 0) (<= k 3))) ; AVOIDING arbitrary list length
  (term ,σ))

;;(error (err val)) ; an error
(define (a-error)
  (term (err ,(a-val))))

;;(not-bool loc number undefined null (ref loc)) ; For malformed "if" error AVOIDING strings
(define (a-not-bool)
  (term ,(choose* (a-loc) (a-number) (the-undefined) (the-null) `(ref ,(a-loc)))))

;;(not-ref loc prim) ; For malformed set! etc.
(define (a-not-ref)
  (term ,(choose* (a-loc) (a-prim))))

;;(e val error (set! e e) (alloc e) (deref e) (if e e e) (begin e e ...)) ; expressions(AVOIDING x)

(define (a-e)
  (define (a-e-limit r)
    (define (a-begin r)
      (define-symbolic* k integer?)
      (define begin (take (list (a-e-limit r)
                                (a-e-limit r)
                                (a-e-limit r))
                          k))
      (assert (and (>= k 0) (<= k 3))) ; AVOIDING arbitrary list length
      (term ,begin))
    (if (= r 0)
        (term ,(choose* (a-val) (a-error)))
        (term ,(choose* (a-val)
                        (a-error)
                        `(set! ,(a-e-limit (- r 1)) ,(a-e-limit (- r 1)))
                        `(alloc ,(a-e-limit (- r 1)))
                        `(deref ,(a-e-limit (- r 1)))
                        `(if ,(a-e-limit (- r 1)) ,(a-e-limit (- r 1)) ,(a-e-limit (- r 1)))
                        (a-begin (- r 1))))))
  (a-e-limit 3)) ; AVOIDING arbitrary recursion depth

(define (synth-term phi?)
  (current-bitwidth #f)
  (clear-asserts!)
  ;; problem 1: this is a program that produces a term, not a declaration...
  (define some-term (a-e))
  ;; problem 2: how do i state properties without a pattern variable / types to reference?!
  ;; problem 3: how does quantification work here?
  (define sol (solve (assert (phi? some-term))))
  (printf "~a~n" sol)
  (and (not (unsat? sol)) (evaluate some-term sol)))

(define (solve1) (synth-term (lambda (e) (number? e))))
(define (solve2) (synth-term (lambda (e) (> (length e) 3))))

