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
  (board/su ::= (any ((pos/su ...) ...)) ((pos/su ...) ...)))

;; is there a better way to redex over rosette's symbolic unions?
;; i would hope we would just have to define some lifts of redex functions
(define (unlift/pos p)
  (cond ((union? p) (map (lambda (g.v) (list (car g.v) (cdr g.v)))
                         (union-contents p)))
        (else (list (list #t p)))))
(define (unlift/board p**)
  (map (lambda (p*) (map unlift/pos p*)) p**))

(define (lift/pos p/su)
  (cond ((<= (length p/su) 1) (second (first p/su)))
        (else (apply union
                     (map (lambda (g.v) (cons (first g.v) (second g.v)))
                          p/su)))))
(define (lift/board guard.board)
  (define guard (first guard.board))
  (define board (map (lambda (p*/su) (map lift/pos p*/su)) (second guard.board)))
  (list guard board))

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

(define-term mediumwin-board
  ((█ █ ○ ○ ○ █ █)
   (█ █ ○ ○ ○ █ █)
   (○ ● ● ○ ○ ● ○)
   (○ ○ ○ ○ ○ ○ ●)
   (○ ○ ○ ○ ● ● ○)
   (█ █ ○ ○ ○ █ █)
   (█ █ ○ ○ ○ █ █)))

(define-term easywin-board
  ((█ █ ○ ○ ○ █ █)
   (█ █ ○ ○ ○ █ █)
   (○ ○ ○ ○ ○ ● ○)
   (○ ○ ○ ○ ○ ○ ●)
   (○ ○ ○ ○ ● ● ○)
   (█ █ ○ ○ ○ █ █)
   (█ █ ○ ○ ○ █ █)))

(define-term oneplaytowin-board
  ((█ █ ○ ○ ○ █ █)
   (█ █ ○ ○ ○ █ █)
   (○ ○ ○ ○ ○ ○ ○)
   (○ ○ ○ ○ ○ ○ ○)
   (○ ○ ○ ○ ● ● ○)
   (█ █ ○ ○ ○ █ █)
   (█ █ ○ ○ ○ █ █)))

(define-term won-board
  ((█ █ ○ ○ ○ █ █)
   (█ █ ○ ○ ○ █ █)
   (○ ○ ○ ○ ○ ○ ○)
   (○ ○ ○ ○ ○ ○ ○)
   (○ ○ ○ ○ ○ ○ ●)
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
   (--> (side-condition (any_1
                         ...
                         (any_2 ...
                          (any_11 ... (any_101 ●) any_12 ...)
                          (any_13 ... (any_102 ●) any_14 ...)
                          (any_15 ... (any_103 ○) any_16 ...)
                          any_3 ...)
                         any_4
                         ...)
                        (and (term any_101) (term any_102) (term any_103)))
        ((and any_101 any_102 any_103)
         (any_1
          ...
          (any_2 ...
           (any_11 ... (any_101 ○) any_12 ...)
           (any_13 ... (any_102 ○) any_14 ...)
           (any_15 ... (any_103 ●) any_16 ...)
           any_3 ...)
          any_4
          ...))
        →)
   (--> (side-condition (any_1
                         ...
                         (any_2 ...
                          (any_11 ... (any_101 ○) any_12 ...)
                          (any_13 ... (any_102 ●) any_14 ...)
                          (any_15 ... (any_103 ●) any_16 ...)
                          any_3 ...)
                         any_4
                         ...)
                        (and (term any_101) (term any_102) (term any_103))) 
        ((and any_101 any_102 any_103)
         (any_1
          ...
          (any_2 ...
           (any_11 ... (any_101 ●) any_12 ...)
           (any_13 ... (any_102 ○) any_14 ...)
           (any_15 ... (any_103 ○) any_16 ...)
           any_3 ...)
          any_4
          ...))
        ←)
   (--> (side-condition (any_1
                         ...
                         (any_2 ..._1 (any_11 ... (any_101 ●) any_12 ...) any_3 ...)
                         (any_4 ..._1 (any_13 ... (any_102 ●) any_14 ...) any_5 ...)
                         (any_6 ..._1 (any_15 ... (any_103 ○) any_16 ...) any_7 ...)
                         any_8
                         ...)
                        (and (term any_101) (term any_102) (term any_103)))
        ((and any_101 any_102 any_103)
         (any_1
          ...
          (any_2 ... (any_11 ... (any_101 ○) any_12 ...) any_3 ...)
          (any_4 ... (any_13 ... (any_102 ○) any_14 ...) any_5 ...)
          (any_6 ... (any_15 ... (any_103 ●) any_16 ...) any_7 ...)
          any_8
          ...))
        ↓)
   (--> (side-condition (any_1
                         ...
                         (any_2 ..._1 (any_11 ... (any_101 ○) any_12 ...) any_3 ...)
                         (any_4 ..._1 (any_13 ... (any_102 ●) any_14 ...) any_5 ...)
                         (any_6 ..._1 (any_15 ... (any_103 ●) any_16 ...) any_7 ...)
                         any_8
                         ...)
                        (and (term any_101) (term any_102) (term any_103)))
        ((and any_101 any_102 any_103)
         (any_1
          ...
          (any_2 ... (any_11 ... (any_101 ●) any_12 ...) any_3 ...)
          (any_4 ... (any_13 ... (any_102 ○) any_14 ...) any_5 ...)
          (any_6 ... (any_15 ... (any_103 ○) any_16 ...) any_7 ...)
          any_8
          ...))
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

(define (Ycombinator board)
  (define value (unlift/board board))
  ;(apply printf "~n~a~n~a~n~a~n~a~n~a~n~a~n~a~n" value)
  (append (apply-reduction-relation move/su value)
          (list (list #f value))))

;; currently explores entire search space, use additional guards to navigate?
(define (Xcombinator boards)
  (define board (lift/board (first boards)))
  (define guard (first board))
  (define sol (solve (begin (clear-asserts!) (assert guard))))
  (define value (evaluate (second board) sol))
  (cond ((> (length boards) 1)
         (define-symbolic* b boolean?)
         ;; new guard expr not simplified???
         (if (and b guard) value (Xcombinator (rest boards))))
        (else value)))

(define (YXcombinator board)
  (Xcombinator (Ycombinator board)))

(define (solve/su board phi?)
  (define sol (synthesize #:forall (list )
                          #:guarantee (assert (phi? board))))
  (and (not (unsat? sol)) (evaluate board sol)))

(define (search/su board phi?)
  (define found? (solve/su board phi?))
  (cond (found? (apply printf "~n~a~n~a~n~a~n~a~n~a~n~a~n~a~n" found?))
        (else
         (printf "~a~n" found?)
         (search/su (YXcombinator board) phi?))))

;(search/su (term oneplaytowin-board) winning?)
;(search/su (term easywin-board) winning?)
(search/su (term mediumwin-board) winning?)
;; move/su currently does not check guard values in match, which allows unsound reduction
;; unsound reductions are bloating search space, but rosette avoids unsound results when solving
;; can't solve the following because it takes too long (search space, symbolic union size, search alg)
;(search/su (term initial-board) winning?)