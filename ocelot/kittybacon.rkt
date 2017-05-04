#lang rosette
(require ocelot)

; Relations
(define rCat (declare-relation 1 "Cat : Cat"))
(define rKittyBacon (declare-relation 1 "one KittyBacon : extends Cat"))
(define rFriends (declare-relation 2 "Cat.friends : Cat -> Cat"))
; Functions / Predicates / Asserts
; TODO type system structs
(define (F c)
  (join c rFriends))
(define (FF c)
  (- (- (F (F c)) (F c)) c))
(define (FFF c)
  (- (- (- (F (F (F c))) (F (F c))) (F c)) c))
(define (CONNECTIONSOF c)
  (+ (+ (F c) (F (F c))) (F (F (F c)))))
(define (CONNECTED)
  (= (- rCat rKittyBacon) (CONNECTIONSOF rKittyBacon)))
(define (SCONNECTED)
  (in (- rCat rKittyBacon) (join rKittyBacon (^ rFriends))))
(define (ISSUPERCONNECTED)
  (and (=> (CONNECTED) (SCONNECTED))
       (=> (SCONNECTED) (CONNECTED))))
; Facts
; TODO type system macros
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
; TODO type system w/ optimal bound semantics of 'one sig', 'extends', 'exactly'...
(define uCat (build-list 5 (lambda (v) (gensym "Cat"))))
(define uKittyBacon uCat)
(define U (universe (append uCat uKittyBacon)))
; Bounds
(define bCat (make-exact-bound rCat (map list uCat)))
(define bKittyBacon (make-upper-bound rKittyBacon (map list uCat)))
(define bFriends (make-product-bound rFriends uCat uCat))
(define B (bounds U (list bCat bKittyBacon bFriends)))
; Interpretations
(define I (instantiate-bounds B))

; Commands
(define (RUN assume query verify/solve?)
  (let* ([ocelot (=> assume query)]
         [rosette (interpret* ocelot I)]
         [cmd (assert rosette)]
         [res (if verify/solve? (verify cmd) (solve cmd))])
    (if (unsat? res) res (interpretation->relations (evaluate I res)))))
(define (verifyISSUPERCONNECTED) (RUN (and fFriends
                                           fKittyBacon
                                           fNoFriendlessCats
                                           fNoSelfFriendship
                                           fSymmetricFriendship)
                                      (ISSUPERCONNECTED)
                                      #f))
; Models
; TODO pretty printer
(verifyISSUPERCONNECTED)
