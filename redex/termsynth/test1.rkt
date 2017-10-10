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
(define (solve2) (synth-term (lambda (e) (equal? (the-null) e))))

#|
The following is a *specification* of all possible terms, with a simple property

Notice how this is basically the asserts defined in the program above
This is better because it seperates the theory of TYPES and VALUES
|#

;;(prim number #t #f undefined null) ; primitives: nums, AVOIDING strs, bools, undef, null
(define (true? t) (and (boolean? t) t))
(define (false? t) (and (boolean? t) (not t)))
(define (symundefined? t) (eq? 'undefined t))
(define (symnull? t) (eq? 'null t))
(define (prim? t)
  (or (number? t)
      (true? t)
      (false? t)
      (symundefined? t)
      (symnull? t)))

;;(loc natural) ; a heap location
(define (natural? t) (and (integer? t) (>= t 0)))
(define (loc? t)
  (natural? t))

;;(val prim (ref loc)) ; a value is a primitive or a heap reference
(define (ref.loc? t)
  (define (symref? t) (eq? 'ref t))
  ; QUESTION: what's the best way to encode "there are only 2 subterms in t"
  ; don't want to get deep into the theory of lists (we shouldn't have to!), staying inductive
  (and (symref? (first t))
       (loc? (first (rest t)))
       (empty? (rest (rest t)))))
(define (val? t)
  (or (prim? t)
      (ref.loc? t)))

;;(σ ((loc val) ...)) ; a heap
(define (loc.val? t)
  (define (symloc? t) (eq? 'loc t))
  (and (symloc? (first t))
       (val? (first (rest t)))
       (empty? (rest (rest t)))))
(define (σ? t)
  (or (empty? t)
      (and (loc.val? (first t))
           (σ? (rest t))))) ;; skolem depth doing it's wonders here for handling ...

;;(error (err val)) ; an error
(define (err.val? t)
  (define (symerr? t) (eq? 'err t))
  (and (symerr? (first t))
       (val? (first (rest t)))
       (empty? (rest (rest t)))))
(define (error? t)
  (err.val? t))

;;(not-bool loc number undefined null (ref loc)) ; For malformed "if" error AVOIDING strings
(define (not-bool? t)
  (or (loc? t)
      (number? t)
      (symundefined? t)
      (symnull? t)
      (ref.loc? t)))

;;(not-ref loc prim) ; For malformed set! etc.
(define (not-ref? t)
  (or (loc? t)
      (prim? t)))

;;(e val error (set! e e) (alloc e) (deref e) (if e e e) (begin e e ...)) ; expressions(AVOIDING x)
(define (set!? t)
  (define (symset!? t) (eq? 'set! t))
  (and (symset!? (first t))
       (e? (first (rest t)))
       (e? (first (rest (rest t))))
       (empty? (rest (rest (rest t))))))
(define (alloc? t)
  (define (symalloc? t) (eq? 'alloc t))
  (and (symalloc? (first t))
       (e? (first (rest t)))
       (empty? (rest (rest t)))))
(define (deref? t)
  (define (symderef? t) (eq? 'deref t))
  (and (symderef? (first t))
       (e? (first (rest t)))
       (empty? (rest (rest t)))))
(define (if? t)
  (define (symif? t) (eq? 'if t))
  (and (symif? (first t))
       (e? (first (rest t)))
       (e? (first (rest (rest t))))
       (e? (first (rest (rest (rest t)))))
       (empty? (rest (rest (rest (rest t)))))))
(define (begin? t)
  (define (symbegin? t) (eq? 'begin t))
  (define (listofe? t) (or (empty? t)
                           (and (e? (first t))
                                (listofe? (rest t))))) ;; notice listof_ always takes the same form
  (and (symbegin? (first t))
       (e? (first (rest t)))
       (listofe? (rest (rest t)))))
(define (e? t)
  (or (val? t)
      (error? t)
      (set!? t)
      (alloc? t)
      (deref? t)
      (if? t)
      (begin? t)))

;; PROBLEM: how do i say "some term" if i have no procedure to generate all terms, only a type spec?
;; if these TERM -> BOOL functions were declared in SMT, couldn't we just assert one and solve?
;; MAJOR PROBLEM is TERM is not a defined sort (in rosette terms, solvable type)
;; can't define these functions as symbolic functions (~> integer? boolean?) without that support
