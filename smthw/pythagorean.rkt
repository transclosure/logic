#lang rosette/safe

(current-bitwidth #f)
(define % remainder)

; variables for Euclid's formula
(define-symbolic m integer?)
(define-symbolic n integer?)

; variables for Pythagorean triple
(define-symbolic x integer?)
(define-symbolic y integer?)
(define-symbolic z integer?)

;; DO NOT MODIFY ABOVE THIS LINE

; global section: add assertions across Part 1 and Part 2 here
(define (euclid-bounds m n) (and (> n 0) (> m n)))
(define (euclid-x m n) (- (* m m) (* n n)))
(define (euclid-y m n) (* (* m n) 2))
(define (euclid-z m n) (+ (* m m) (* n n)))
(define-symbolic anint integer?)
(define (coprime a b) (exists (list anint) (= (% (* b anint) a) 1)))
; end assertions across Part 1 and Part 2

(define (part1)
  ; add assertions and/or declare additional symbols
  ; for part1 here
  (define euclid-correct
    (implies (and (euclid-bounds m n)
                  (= x (euclid-x m n))
                  (= y (euclid-y m n))
                  (= z (euclid-z m n)))
             (= (+ (* x x) (* y y)) (* z z))))
  ; end assertions for part1
  ; write down a formula for verification
  (verify (assert euclid-correct)))
; replace ... in `part1-interp` with
; - `sat?` if `solve` in `part1` returning a model means the formula works
; - `unsat?` if `solve` in `part1` returning unsat means the formula works
(define part1-interp unsat?) 

(define (part2)
  ; add assertions and/or declare additional symbols
  ; for part2 here
  (define euclid-nonprimitive
    (and (euclid-bounds m n)
         (= x (euclid-x m n))
         (= y (euclid-y m n))
         (= z (euclid-z m n))
         (or (not (coprime x y))
             (not (coprime y z))
             (not (coprime x z)))))
  ; end assertions for part2
  ; write down a formula to test the hypothesis
  (solve (assert euclid-nonprimitive)))
; replace ... in `part2-interp` with
; - `sat?` if `solve` in `part2` returning a model means
;   it can produce non-primitive
; - `unsat?` if `solve` in `part2` returning unsat means
;   it can produce non-primitive
(define part2-interp sat?)

;; DO NOT MODIFY BELOW THIS LINE

(define-values (part1-val _1) (with-asserts (part1)))
(define-values (part2-val _2) (with-asserts (part2)))

(printf "According to your interpretation\n")
; expect to see yes and yes
(printf "Part 1: ~a, Formula works?: ~a\n"
        part1-val (if (part1-interp part1-val) "yes" "no"))
(printf "Part 2: ~a, Can produce non-primitive?: ~a\n"
        part2-val (if (part2-interp part2-val) "yes" "no"))
