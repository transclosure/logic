#lang rosette
(require ocelot)

; Relations
(define rCat (declare-relation 1 "Cat : Cat"))
(define rFriends (declare-relation 2 "Cat.friends : Cat -> Cat"))
; Forumlas
(define fFriends (and
                  (in (join rFriends univ) rCat)
                  (in (join univ rFriends) rCat)))
(define fNoFriendlessCats (no ([c rCat])
                              (no (join c rFriends))))
(define fNoSelfFriendship (no ([c rCat])
                              (in c (join c rFriends))))
(define fSymmetricFriendship (= rFriends (~ rFriends)))

; Universes
(define uCat (build-list 4 (lambda (v) (gensym "Cat"))))
(define U (universe (append uCat)))
; Bounds
(define bCat (make-upper-bound rCat (map list uCat)))
(define bFriends (make-product-bound rFriends uCat uCat))
(define B (bounds U (list bCat bFriends)))
; Interpretations
(define I (instantiate-bounds B))

; Commands
(define c1 (solve (assert (interpret* (and (some rCat)
                                       fFriends
                                           fNoFriendlessCats
                                           fNoSelfFriendship
                                           fSymmetricFriendship)
                                      I))))
; Models
(define m1 (interpretation->relations (evaluate I c1)))
m1
