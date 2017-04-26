#lang rosette/safe

(require "cs1950y.rkt")
(require "bsearch-definitions.rkt")

(provide (all-defined-out))

; length of the vector subject to 0 <= len <= 64.
; Note that this is the input and is not a part of
; the algorithm; you should not try to break it.
(define len 30)

; INSTRUCTION: Clone this file to bsearch1.rkt, ...,
; bsearch5.rkt. Only change functions below to break the
; verification.

; next :: state -> state
; return the next state following the algorithm
(define-match (next (state A x l r ans))
  ; let m = floor((l + r) / 2)
  (define m (quotient (+ l r) 2))
  ; let e = A[m]
  (define e (vector-ref A m))
  (cond
    ; if e = x, then ans := m
    [(= e x) (set! ans m)]
    ; if e < x, then l := m + 1
    [(< e x) (set! l (add1 m))]
    ; if e > x, then r := m - 1
    [(> e x) (set! r (sub1 m))])
  (state A x l r ans))

; initial-state :: vectorof number, number -> state
; return the initial state, given the input
; here, we have
; 1. l := 0
; 2. r := len(A) - 1
; 3. ans = -1
; in the beginning, so these are the initial state
(define (initial-state A x)
  (state A x (sub1 (vector-length A)) (sub1 (vector-length A)) -1))

; measure :: state -> number
; return the measure of a state
(define-match (measure (state _ _ l r ans))
  (cond
    ; if ans != -1, then the measure is 0
    [(not (= ans -1)) 0]
    ; otherwise, the measure is r - l + 1
    [else (+ r (- l) 1)]))
