#lang rosette

(require "cs1950y.rkt")
(require "bsearch-definitions.rkt")

; modify this to run your files e.g., bsearch1.rkt
(require "bsearch0.rkt")

; INSTRUCTION: do not modify anything besides the above line

(define time-begin (current-seconds))

; index-of :: listof number, number -> number
; return an index i where lst[i] = x
(define (index-of lst x)
  (define (iter now lst)
    (match lst
      ; note that :: is just cons
      [(:: f r) (if (= f x) now (iter (add1 now) r))]
      [else #f]))
  (iter 0 lst))

; sorted? :: vectorof number -> bool
; return whether the vector is sorted in ascending order
(define (sorted? A)
  (define (iter lst)
    (match lst
      [(:: f (:: s r)) (and (<= f s) (iter (:: s r)))]
      [else #t]))
  (iter (vector->list A)))

; create A as a vector of length len where each element
; is an integer symbol. Use define-symbolic* so that
; Z3 creates different symbols for each element
(define A (for/vector ([i len])
            (define-symbolic* e integer?) e))

; since we want to talk about binary search algorithm,
; we assert that A must be sorted as a fact
(assert (sorted? A))

; create a symbol x as an element to find
(define-symbolic x integer?)

; invariant-hold? :: state -> bool
; return whether the invariant holds on a given state
(define-match (invariant-hold? (state A x l r ans))
  (define lst (vector->list A))

  ; has-elem is a bool indicates whether the element that
  ; we are looking for, which is x, is in the vector A
  (define has-elem (member x lst))

  ; has-found is a bool indicates whether at this state we
  ; have found x
  (define has-found (not (= ans -1)))

  ; invariants:
  ; 1. 0 <= l <= r + 1 <= |A|
  ; 2. if l > r and x is in fact in A, then we must have
  ;    found x
  ; 3. if we have found x, then it must be correct i.e.,
  ;    A[ans] = x
  ; 4. if l <= r and x is in fact in A and we have not found
  ;    the answer, then the algorithm is not terminating yet,
  ;    so the range [l, r] should contains x
  (and (<= 0 l (add1 r) (vector-length A))
       (implies (and (> l r) has-elem) has-found)
       (implies has-found (= x (vector-ref A ans)))
       (implies (and (<= l r) (not has-found) has-elem)
                (<= l (index-of lst x) r))))

; correct? :: state -> bool
; return whether the state's ans is correct
(define-match (correct? (state A x _ _ ans))
  (define lst (vector->list A))
  (cond
    ; if ans = -1, then x should not be in A
    [(= ans -1) (not (member x lst))]
    ; otherwise, A[ans] should be x
    [else (= x (vector-ref A ans))]))

(~ ["1. Initially the invariant holds: ~a\n"]
   (verify (assert (invariant-hold? (initial-state A x)))))

; create l, r, ans, and pack them together as a state any-s
(define-symbolic* l integer?)
(define-symbolic* r integer?)
(define-symbolic* ans integer?)
(define any-s (state A x l r ans))

(~ ["2. For any state where the invariant holds, the measure "
    "is a natural number: ~a\n"]
   (verify #:assume (assert (invariant-hold? any-s))
           #:guarantee (assert (<= 0 (measure any-s)))))

(~ ["3. For any state where the invariant holds and "
    "is not the last state, the invariant holds for the "
    "next state too (that is, transition preserves the "
    "invariant): ~a\n"]
   (verify
    #:assume
    (assert (and (< 0 (measure any-s))
                 (invariant-hold? any-s)))
    #:guarantee
    (assert (invariant-hold? (next any-s)))))

(~ ["4. For any state where the invariant holds and "
    "is not the last state, the measure for the next state "
    "is less than the current measure: ~a\n"]
   (verify #:assume
           (assert (and (< 0 (measure any-s))
                        (invariant-hold? any-s)))
           #:guarantee
           (assert (< (measure (next any-s))
                      (measure any-s)))))

(~ ["5. For any last state where the invariant holds, "
    "the algorithm produces a correct output: ~a\n"]
   (verify #:assume (assert (and (= (measure any-s) 0)
                                 (invariant-hold? any-s)))
           #:guarantee (assert (correct? any-s))))

(~ ["Time elapsed: ~a\n"]
   (- (current-seconds) time-begin))

; combining everything together, we obtain the algorithm
(define (bsearch A x)
  ; define the initial state
  (define s (initial-state A x))
  ; while the algorithm shouldn't terminate, get the next state
  (while (> (measure s) 0)
         (set! s (next s)))
  ; return the answer
  (state-ans s))

; Below is how you would call the binary search function on a concrete value.
; Feel free to copy it to the REPL and try it out.
; However, please don't uncomment when submitting to prevent an infinite loop
; that might happen.

; (bsearch #(1 5 7 10 10 123) 10)
