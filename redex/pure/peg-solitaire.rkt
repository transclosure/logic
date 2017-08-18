#lang rosette/safe

(require redex)
(require rosette/query/debug
         rosette/lib/render
         rosette/lib/synthax)
(current-bitwidth #f)

#|||||||||||
| Language |
|||||||||||#

(define-language peg-solitaire
  (pos ::= █ ○ ●) 
  (board ::= ((pos ...) ...)))

#||||||||
| Terms |
||||||||#

(define-synthax (a7x7board depth)
  #:base (choose '○ '●)
  #:else
  `((█ █,(choose '○ '●),(choose '○ '●),(choose '○ '●)█ █)
    (█ █,(choose '○ '●),(choose '○ '●),(choose '○ '●)█ █)
    (,(choose '○ '●),(choose '○ '●),(choose '○ '●),(choose '○ '●)
                    ,(choose '○ '●),(choose '○ '●),(choose '○ '●))
    (,(choose '○ '●),(choose '○ '●),(choose '○ '●),(choose '○ '●)
                    ,(choose '○ '●),(choose '○ '●),(choose '○ '●))
    (,(choose '○ '●),(choose '○ '●),(choose '○ '●),(choose '○ '●)
                    ,(choose '○ '●),(choose '○ '●),(choose '○ '●))
    (█ █,(choose '○ '●),(choose '○ '●),(choose '○ '●)█ █)
    (█ █,(choose '○ '●),(choose '○ '●),(choose '○ '●)█ █))
  )
           
(define-term initial-board
  ((█ █ ● ● ● █ █)
   (█ █ ● ● ● █ █)
   (● ● ● ● ● ● ●)
   (● ● ● ○ ● ● ●)
   (● ● ● ● ● ● ●)
   (█ █ ● ● ● █ █)
   (█ █ ● ● ● █ █)))

(define-term oneplaytowin-board
  ((█ █ ○ ○ ○ █ █)
   (█ █ ○ ○ ○ █ █)
   (○ ○ ○ ○ ○ ○ ○)
   (○ ○ ○ ○ ○ ○ ○)
   (○ ○ ○ ○ ● ● ○)
   (█ █ ○ ○ ○ █ █)
   (█ █ ○ ○ ○ █ █)))

(define-term lost-board
  ((█ █ ○ ○ ○ █ █)
   (█ █ ○ ○ ○ █ █)
   (○ ○ ○ ● ○ ○ ○)
   (○ ○ ○ ○ ○ ○ ○)
   (○ ○ ○ ○ ○ ● ○)
   (█ █ ○ ○ ○ █ █)
   (█ █ ○ ○ ○ █ █)))

(define-term won-board
  ((█ █ ○ ○ ○ █ █)
   (█ █ ○ ○ ○ █ █)
   (○ ○ ○ ○ ○ ○ ○)
   (○ ○ ○ ○ ○ ○ ○)
   (○ ○ ○ ○ ○ ● ○)
   (█ █ ○ ○ ○ █ █)
   (█ █ ○ ○ ○ █ █)))

#|||||||||||||
| Reductions |
|||||||||||||#

(define move
  (reduction-relation
   peg-solitaire
   #:domain board
   (--> (any_1
         ...
         (any_2 ... ● ● ○ any_3 ...)
         any_4
         ...)
        (any_1
         ...
         (any_2 ... ○ ○ ● any_3 ...)
         any_4
         ...)
        →)
   (--> (any_1
         ...
         (any_2 ... ○ ● ● any_3 ...)
         any_4
         ...)
        (any_1
         ...
         (any_2 ... ● ○ ○ any_3 ...)
         any_4
         ...)
        ←)
   (--> (any_1
         ...
         (any_2 ..._1 ● any_3 ...)
         (any_4 ..._1 ● any_5 ...)
         (any_6 ..._1 ○ any_7 ...)
         any_8
         ...)
        (any_1
         ...
         (any_2 ... ○ any_3 ...)
         (any_4 ... ○ any_5 ...)
         (any_6 ... ● any_7 ...)
         any_8
         ...)
        ↓)
   (--> (any_1
         ...
         (any_2 ..._1 ○ any_3 ...)
         (any_4 ..._1 ● any_5 ...)
         (any_6 ..._1 ● any_7 ...)
         any_8
         ...)
        (any_1
         ...
         (any_2 ... ● any_3 ...)
         (any_4 ... ○ any_5 ...)
         (any_6 ... ○ any_7 ...)
         any_8
         ...)
        ↑)))

#||||||||||||||||||
| Term Properties |
||||||||||||||||||#

(define/debug (winning? board)
  (define/debug pegs-left-on-board
    (count (curry equal? '●) (flatten board)))
  (= pegs-left-on-board 1))

#||||||||||||||||||||||||||
| Term Reduction Checking |
||||||||||||||||||||||||||#

(define (find-rewrite oldboard phi?)
  (define newboard (a7x7board 1))
  (define sol (synthesize #:forall (list )
                          #:guarantee (assert
                                       (and (equal? (YXcombinator oldboard) newboard)
                                            (phi? newboard)))))
  (and (not (unsat? sol)) (evaluate newboard sol)))

(define (YXcombinator board)
  ;; for some reason choose cannot be used in context of racket/apply (unfolding)
  (define (chooseboard boards)
    (cond ((equal? (length boards) 1) (first boards))
          (else (choose (first boards) (chooseboard (rest boards))))))
  (chooseboard (apply-reduction-relation move board)))

;; finding a single step rewrite is easy!
(apply printf (cons "~n~a~n~a~n~a~n~a~n~a~n~a~n~a~n"
                    (find-rewrite (term oneplaytowin-board) winning?)))
;; redex is good at recursion down the tree (Ycombinator)
;; rosette is good at disjunction across the tree (Xcombinator)
;; Xcombinator is what I'm calling Emina's SVM that squishes (choose terms) into a single term
;; example of it here
(YXcombinator (term initial-board))
;; but oh no! we can't do multi-step Y reduction because X combined terms aren't in the language!
(YXcombinator (YXcombinator (term initial-board)))
;; well... they're just subterms, and if my limited knowledge of PL is correct...
;; all we have to do is extend the language with a SMT compatible closure to match/reduce these terms
;; this may be more difficult in general, but for now, I can just extend peg-solitaire with the few
;; disjunctive cases
