#lang rosette
(require ocelot)

; Universe of Discourse
(require "DISCOURSE.rkt")
(declare-sig #t 3 "Cat")
(declare-sig #t 1 "KittyBacon" "Cat")
(declare-rel "Cat" 2 "friends")
; Functions / Predicates / Asserts
(define (F c)
  (join c (THIS "friends")))
(define (FF c)
  (- (- (F (F c)) (F c)) c))
(define (FFF c)
  (- (- (- (F (F (F c))) (F (F c))) (F c)) c))
(define (CONNECTIONSOF c)
  (+ (+ (F c) (FF c)) (FFF c)))
(define (CONNECTED)
  (= (- (THIS "Cat") (THIS "KittyBacon")) (CONNECTIONSOF (THIS "KittyBacon"))))
(define (SCONNECTED)
  (= (- (THIS "Cat") (THIS "KittyBacon")) (join (THIS "KittyBacon") (^ (THIS "friends")))))
(define (ISSUPERCONNECTED)
  (and (=> (CONNECTED) (SCONNECTED))
       (=> (SCONNECTED) (CONNECTED))))
; Facts
(define fNoFriendlessCats
  (no ([c (THIS "Cat")])
      (no (join c (THIS "friends")))))
(define fNoSelfFriendship
  (no ([c (THIS "Cat")])
      (in c (join c (THIS "friends")))))
(define fSymmetricFriendship
  (= (THIS "friends") (~ (THIS "friends"))))
; Models
(define (verifyISSUPERCONNECTED)
  (declare-cmd (and fNoFriendlessCats
                    fNoSelfFriendship
                    fSymmetricFriendship
                    (not (ISSUPERCONNECTED)))
               #t))
(verifyISSUPERCONNECTED)

