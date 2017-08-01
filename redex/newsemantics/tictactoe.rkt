#lang racket

(require redex)
(provide )

;; how can we specify things in redex?
;;;; language = specifies the model space (how much meta/invalid is in the space is up to you)
;;;; redex reduction relations = quasi-geometric implications (does not support permutation?) 
;;;; side conditions = redex-match with more expressive power (arbitrary code in LHS of implication) 
;;;; search algorithm = a loop with a bunch of side conditions not tied to a redex-match

;; board validity must remain undefined, unless you have a context sensitive language
;;;; redex, like spin, does not constrain the model space, but the transition choices
;;;; razor only constrains the model space because it restricts meta transition choices

;; move validity can be defined, depends on how meta you want your model space
;;;; defining only valid move reduction relations -> only transition from valid to valid
;;;; defining all move reduction relations -> transitions to invalid models, prune search instead

;; redex is purely positve, negation supported like it was in Razor
;;;; negation on LHS -> disjunction on RHS -> side condition
;;;; negation on RHS -> complement relation positive fact -> relation and complement implies falsehood
;;;; purely negative constraint -> match implies falsehood
;;;; positive falsehood is a state with no outward reductions

;; redex LHS variable matching is purely ordered
;;;; permutation supported through enumeration of all possible combinations
;;;; you need symmetric forward, backward, and center(equal) matching rules for each transition
;;;; see next/move for a concrete example

;; theory of equality (which includes LHS variable matching) is hard!
;;;; razor didnt handle it well (that's why transitive closure was intractable)
;;;; holding off for now

(define-language TICTACTOE/L
  ;; util/ordering[Board]
  ;; redex gives you this for free (via positive only transitions over a single board)
  ;; theory of equality unsupported, single board until equality can be specified
  (INSTANCE ::= ((INDEX ...) (PLAYER ...) (PLAYER BOARD)) (FALSEHOOD))
  ;; sig Board { ...
  (BOARD ::= (PLACES ...))
  ;; places: Index -> Index -> Player
  (PLACES ::= (INDEX INDEX PLAYER))
  ;; abstract sig Index {} ... one sig Three extends Index {}
  (INDEX ::= 1 2 3)
  ;; abstract sig Player {} .... one sig O extends Player {}
  (PLAYER ::= X O)
  )

(define TICTACTOE/T+
  (reduction-relation
   TICTACTOE/L #:domain INSTANCE
   ;; some p=turn=X, some r,c (enumerated), next/move(p, r, c)
   (--> ((INDEX_1 ...
          INDEX_2
          INDEX_3 ...
          INDEX_4
          INDEX_5 ...) (PLAYER ...) (X (PLACES_1 ...)))
        ((INDEX_1 ...
          INDEX_2
          INDEX_3 ...
          INDEX_4
          INDEX_5 ...) (PLAYER ...) (O (PLACES_1 ...
                                 (INDEX_2 INDEX_4 X))))
        "next/move[p=X, r<c]"
        )
   (--> ((INDEX_1 ...
          INDEX_2
          INDEX_3 ...) (PLAYER ...) (X (PLACES_1 ...)))
        ((INDEX_1 ...
          INDEX_2
          INDEX_3 ...) (PLAYER ...) (O (PLACES_1 ...
                                 (INDEX_2 INDEX_2 X))))
        "next/move[p=X, r=c]"
        )
   (--> ((INDEX_1 ...
          INDEX_2
          INDEX_3 ...
          INDEX_4
          INDEX_5 ...) (PLAYER ...) (X (PLACES_1 ...)))
        ((INDEX_1 ...
          INDEX_2
          INDEX_3 ...
          INDEX_4
          INDEX_5 ...) (PLAYER ...) (O (PLACES_1 ...
                                 (INDEX_4 INDEX_2 X))))
        "next/move[p=X, r>c]"
        )
   ;; some p=turn=O, some r,c (enumerated), next/move(p, r, c)
   (--> ((INDEX_1 ...
          INDEX_2
          INDEX_3 ...
          INDEX_4
          INDEX_5 ...) (PLAYER ...) (O (PLACES_1 ...)))
        ((INDEX_1 ...
          INDEX_2
          INDEX_3 ...
          INDEX_4
          INDEX_5 ...) (PLAYER ...) (X (PLACES_1 ...
                                 (INDEX_2 INDEX_4 O))))
        "next/move[p=O, r<c]"
        )
   (--> ((INDEX_1 ...
          INDEX_2
          INDEX_3 ...) (PLAYER ...) (O (PLACES_1 ...)))
        ((INDEX_1 ...
          INDEX_2
          INDEX_3 ...) (PLAYER ...) (X (PLACES_1 ...
                                 (INDEX_2 INDEX_2 O))))
        "next/move[p=O, r=c]"
        )
   (--> ((INDEX_1 ...
          INDEX_2
          INDEX_3 ...
          INDEX_4
          INDEX_5 ...) (PLAYER ...) (O (PLACES_1 ...)))
        ((INDEX_1 ...
          INDEX_2
          INDEX_3 ...
          INDEX_4
          INDEX_5 ...) (PLAYER ...) (X (PLACES_1 ...
                                 (INDEX_4 INDEX_2 O))))
        "next/move[p=O, r>c]"
        )
   ))

(define TICTACTOE/T-
  (reduction-relation
   TICTACTOE/L #:domain INSTANCE
   (--> ((INDEX ...) (PLAYER ...) (PLAYER_1 (PLACES_1 ...
                                             (INDEX_1 INDEX_2 PLAYER_2)
                                             PLACES_2 ...
                                             (INDEX_1 INDEX_2 PLAYER_3)
                                             PLACES_3 ...)))
        (FALSEHOOD)
        "places: Index -> Index -> lone Player"
        )
   ;; undefined without multiple boards and equality
   #|(--> ((INDEX ...) (PLAYER ...) ((PLAYER_1 ((INDEX_1 INDEX_2 PLAYER_2) PLACES_1 ...))
                        (PLAYER_3 BOARD_1) ...))
        (FALSEHOOD)
        "no first.places"
        )|#
   ))

;; violates places: Index -> Index -> lone Player
(define-term test/invalid ((1 2 3) (X O) (X ((3 3 X)
                                             (3 3 X)))))
(define-term initial ((1 2) (X O) (X ())))
;; run {} for 10 Board
;; undefined without multiple boards and equality
#|(define-term RUN$1 ((1 2 3) (X O) ((X ())
                                   (O ())
                                   (X ())
                                   (O ())
                                   (X ())
                                   (O ())
                                   (X ())
                                   (O ())
                                   (X ())
                                   (O ()))))|#
;; even with pruning violating instances from further search steps, the search space is huge
;; quick for a 2x2 board (4 fanout, 4 deep)
;; takes forever on a 3x3 board (9 fanout, 9 deep)
(define initials (list (list (term initial))))
(define (search/constrain* instances)
  (define instances-prime (append* (map search/constrain (last instances))))
  (if (empty? instances-prime)
      instances
      (search/constrain* (append instances (list instances-prime)))))
(define (search/constrain instance)
  (filter (λ (i) (empty? (constrain i))) (search instance)))
(define (search instance)
  (apply-reduction-relation TICTACTOE/T+ instance))
(define (constrain instance)
  (apply-reduction-relation TICTACTOE/T- instance))


