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

(define-extended-language peg-solitaire/su
  peg-solitaire
  (pos/su ::= ((any pos) ...))
  (board/su ::= ((pos/su ...) ...)))

;; is there a better way to redex over rosette's symbolic unions?
;; i would hope we would just have to define some lifts of redex functions
(define (unlift/pos p)
  (cond ((union? p) (map (lambda (g.v) (list (car g.v) (cdr g.v)))
                         (union-contents p)))
        (else (list (list #t p)))))
(define (lift/pos p/su)
  (cond ((<= (length p/su) 1) (second (first p/su)))
        (else (apply union
                     (map (lambda (g.v) (cons (first g.v) (second g.v)))
                          p/su)))))
(define (unlift/board p**)
  (map (lambda (p*) (map unlift/pos p*)) p**))
(define (lift/board p**/su)
  (map (lambda (p*/su) (map lift/pos p*/su)) p**/su))

#||||||||
| Terms |
||||||||#

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

(define move/su
  (reduction-relation
   peg-solitaire/su
   #:domain board/su
   (--> (any_1
         ...
         (any_2 ...
          (any_11 ... (any_101 ●) any_12 ...)
          (any_13 ... (any_102 ●) any_14 ...)
          (any_15 ... (any_103 ○) any_16 ...)
          any_3 ...)
         any_4
         ...)
        (any_1
         ...
         (any_2 ...
          (any_11 ... (any_101 ○) any_12 ...)
          (any_13 ... (any_102 ○) any_14 ...)
          (any_15 ... (any_103 ●) any_16 ...)
          any_3 ...)
         any_4
         ...)
        →)
   (--> (any_1
         ...
         (any_2 ...
          (any_11 ... (any_101 ○) any_12 ...)
          (any_13 ... (any_102 ●) any_14 ...)
          (any_15 ... (any_103 ●) any_16 ...)
          any_3 ...)
         any_4
         ...)
        (any_1
         ...
         (any_2 ...
          (any_11 ... (any_101 ●) any_12 ...)
          (any_13 ... (any_102 ○) any_14 ...)
          (any_15 ... (any_103 ○) any_16 ...)
          any_3 ...)
         any_4
         ...)
        ←)
   (--> (any_1
         ...
         (any_2 ..._1 (any_11 ... (any_101 ●) any_12 ...) any_3 ...)
         (any_4 ..._1 (any_13 ... (any_102 ●) any_14 ...) any_5 ...)
         (any_6 ..._1 (any_15 ... (any_103 ○) any_16 ...) any_7 ...)
         any_8
         ...)
        (any_1
         ...
         (any_2 ... (any_11 ... (any_101 ○) any_12 ...) any_3 ...)
         (any_4 ... (any_13 ... (any_102 ○) any_14 ...) any_5 ...)
         (any_6 ... (any_15 ... (any_103 ●) any_16 ...) any_7 ...)
         any_8
         ...)
        ↓)
   (--> (any_1
         ...
         (any_2 ..._1 (any_11 ... (any_101 ○) any_12 ...) any_3 ...)
         (any_4 ..._1 (any_13 ... (any_102 ●) any_14 ...) any_5 ...)
         (any_6 ..._1 (any_15 ... (any_103 ●) any_16 ...) any_7 ...)
         any_8
         ...)
        (any_1
         ...
         (any_2 ... (any_11 ... (any_101 ●) any_12 ...) any_3 ...)
         (any_4 ... (any_13 ... (any_102 ○) any_14 ...) any_5 ...)
         (any_6 ... (any_15 ... (any_103 ○) any_16 ...) any_7 ...)
         any_8
         ...)
        ↑)
   ))

#||||||||||||||||||
| Term Properties |
||||||||||||||||||#

(define/debug (winning? p**)
  (define/debug pegs-left-on-board
    (count (curry equal? '●) (flatten p**)))
  (= pegs-left-on-board 1))

#||||||||||||||||||||||||||
| Term Reduction Checking |
||||||||||||||||||||||||||#

(define (solve/su board/su phi?)
  (define sol (synthesize #:forall (list )
                          #:guarantee (assert (phi? board/su))))
  (and (not (unsat? sol)) (evaluate board/su sol)))

(define (YXcombinator board)
  ;; for some reason choose cannot be used in context of racket/apply (unfolding)
  (define (chooseboard boards)
    (cond ((equal? (length boards) 1) (first boards))
          ;; instead of making the guard an arbitrary choose...
          ;; can we make it a function representing the reduction choice made
          (else (choose (first boards) (chooseboard (rest boards))))))
  (chooseboard (map lift/board (apply-reduction-relation move/su (unlift/board board)))))

;; YXcombinator currently buggy after 1 step... two possible sources...
;; 1. reduction relation for moving symbolic unions is flawed
;; 2. (chooseboard boards) is not properly unioning all the possible boards
;(define board0 (term initial-board))
;(map lift/board (apply-reduction-relation move/su (unlift/board board0)))
;(define board1 (YXcombinator board0))
;(map lift/board (apply-reduction-relation move/su (unlift/board board1)))
;(define board2 (YXcombinator board1))
;(map lift/board (apply-reduction-relation move/su (unlift/board board2)))

(solve/su (YXcombinator (term oneplaytowin-board)) winning?)
