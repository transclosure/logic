#lang rosette
(require ocelot)

; Relations
(define rCat (declare-relation 1 "Cat : Cat"))
(define rKittyBacon (declare-relation 1 "one KittyBacon : extends Cat"))
(define rFriends (declare-relation 2 "Cat.friends : Cat -> Cat"))
; Functions
(define (F c)
  (join c rFriends))
(define (FF c)
  (- (- (F (F c)) (F c)) c))
(define (FFF c)
  (- (- (- (F (F (F c))) (F (F c))) (F c)) c))
(define (connectionsOf c)
  (+ (+ (F c) (F (F c))) (F (F (F c)))))
; Forumlas
(define fFriends
  (and (in (join rFriends univ) rCat)
       (in (join univ rFriends) rCat)))
(define fKittyBacon
  (and (one rKittyBacon)
       (in rKittyBacon rCat)))
(define fNoFriendlessCats
  (no ([c rCat])
      (no (join c rFriends))))
(define fNoSelfFriendship
  (no ([c rCat])
      (in c (join c rFriends))))
(define fSymmetricFriendship
  (= rFriends (~ rFriends)))

; Universes
(define uCat (build-list 4 (lambda (v) (gensym "Cat"))))
(define uKittyBacon uCat)
(define U (universe (append uCat uKittyBacon)))
; Bounds
(define bCat (make-upper-bound rCat (map list uCat)))
(define bKittyBacon (make-upper-bound rKittyBacon (map list uCat)))
(define bFriends (make-product-bound rFriends uCat uCat))
(define B (bounds U (list bCat bFriends bKittyBacon)))
; Interpretations
(define I (instantiate-bounds B))

; Commands
(define c1 (solve (assert (interpret*
                           (and fFriends
                                fKittyBacon
                                fNoFriendlessCats
                                fNoSelfFriendship
                                fSymmetricFriendship)
                           I))))
; Models
(define m1 (interpretation->relations (evaluate I c1)))
m1
