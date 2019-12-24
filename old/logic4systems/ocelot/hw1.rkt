#lang rosette
(require ocelot)

; Relations
(define rR (declare-relation 2 "some r: univ -> univ"))
; Forumlas
(define fNonempty
  (some rR))
(define fTransitive
  (in (join rR rR) rR))
(define fIrreflexive
  (no (& iden rR)))
(define fSymmetric
  (in (~ rR) rR))
(define fFunctional
  (in (join (~ rR) rR) iden))
(define fInjective
  (in (join rR (~ rR)) iden))
(define fTotal
  (in univ (join rR univ)))
(define fOnto
  (in univ (join univ rR)))

; Universes
(define U (universe (build-list 4 values)))
(define uR (universe-atoms U))
; Bounds
(define bR (make-product-bound rR uR uR))
(define B (bounds U (list bR)))
; Interpretations
(define I (instantiate-bounds B))

; Commands
(define c1 (solve (assert (interpret* fNonempty I))))
; Models
(define m1 (interpretation->relations (evaluate I c1)))
m1
