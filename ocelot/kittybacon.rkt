#lang rosette
(require ocelot)

; discourse.rkt
(require racket/format)
(define DISCOURSE (make-hash))
(struct RELATION (THIS SUPER BOUND))
(define (THIS r) (RELATION-THIS (hash-ref DISCOURSE r)))
(define (SUPER r) (RELATION-SUPER (hash-ref DISCOURSE r)))
(define (UNIV upperbound name)
  (build-list upperbound (lambda (i) (string-append name "$" (~a i)))))
(define (UNIV* r)
  (let* ([SUPER (SUPER r)])
    (if (string? SUPER) (UNIV* SUPER) SUPER)))
(define (BOUND r) (RELATION-BOUND (hash-ref DISCOURSE r)))
(define (declare-rel parent arity name)
  (let* ([THIS (declare-relation arity name)]
         [SUPER parent]
         [UNIV (UNIV* SUPER)]
         [BOUND (case arity
                  [(2) (make-product-bound THIS UNIV UNIV)]
                  [else (error "unsupported")])]
         [R (RELATION THIS SUPER BOUND)])
    (hash-set! DISCOURSE name R)))
(define (declare-sig upperbound name [extends ""])
  (let* ([THIS (declare-relation 1 name)]
         [SUPER (case extends
                  [("") (UNIV upperbound name)]
                  [else extends])]
         [UNIV (case extends
                 [("") SUPER]
                 [else (UNIV* SUPER)])] ;TODO optimize upper bound here?
         [BOUND (make-upper-bound THIS (map list UNIV))]
         [R (RELATION THIS SUPER BOUND)])
    (hash-set! DISCOURSE name R)))
(define (declare-cmd ocelot solve/verify?)
  (let* ([U (universe
             ;TODO fix internal hash-map eq? byval vs byref issue...
             (first (append (hash-map DISCOURSE (lambda (name relation) (UNIV* name))))))]
         [B (bounds U (hash-map DISCOURSE
                                (lambda (name relation) (RELATION-BOUND relation))))]
         [I (begin (println B) (instantiate-bounds B))]
         [rosette (interpret* ocelot I)]
         [cmd (assert rosette)]
         [res (if solve/verify? (solve cmd) (verify cmd))]) ;TODO pretty printer
    (if (unsat? res) res (interpretation->relations (evaluate I res)))))

; Universe of Discourse
(declare-sig 2 "Cat")
(declare-sig 1 "KittyBacon" "Cat")
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
