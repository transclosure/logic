#lang rosette

(require redex)
(require rosette/query/debug)

(define-language peg-solitaire
  [position ::= empty peg]
  [empty ::= █ ○]
  [peg ::= ●]
  [board ::= ([position ...] ...)])

(define-term initial-board
  ([█ █ █ █ █ █ █ █ █]
   [█ █ █ ● ● ● █ █ █]
   [█ █ █ ● ● ● █ █ █]
   [█ ● ● ● ● ● ● ● █]
   [█ ● ● ● ○ ● ● ● █]
   [█ ● ● ● ● ● ● ● █]
   [█ █ █ ● ● ● █ █ █]
   [█ █ █ ● ● ● █ █ █]
   [█ █ █ █ █ █ █ █ █]))

(define-term lost-board
  ([█ █ █ █ █ █ █ █ █]
   [█ █ █ ○ ○ ○ █ █ █]
   [█ █ █ ○ ○ ○ █ █ █]
   [█ ○ ○ ○ ● ○ ○ ○ █]
   [█ ○ ○ ○ ○ ○ ○ ○ █]
   [█ ○ ○ ○ ○ ○ ● ○ █]
   [█ █ █ ○ ○ ○ █ █ █]
   [█ █ █ ○ ○ ○ █ █ █]
   [█ █ █ █ █ █ █ █ █]))

(define move
  (reduction-relation
   peg-solitaire
   #:domain board
   (--> (any_1
         ...
         [any_2 ... ● ● ○ any_3 ...]
         any_4
         ...)
        (any_1
         ...
         [any_2 ... ○ ○ ● any_3 ...]
         any_4
         ...)
        →)
   (--> (any_1
         ...
         [any_2 ... ○ ● ● any_3 ...]
         any_4
         ...)
        (any_1
         ...
         [any_2 ... ● ○ ○ any_3 ...]
         any_4
         ...)
        ←)
   (--> (any_1
         ...
         [any_2 ..._1 ● any_3 ...]
         [any_4 ..._1 ● any_5 ...]
         [any_6 ..._1 ○ any_7 ...]
         any_8
         ...)
        (any_1
         ...
         [any_2 ... ○ any_3 ...]
         [any_4 ... ○ any_5 ...]
         [any_6 ... ● any_7 ...]
         any_8
         ...)
        ↓)
   (--> (any_1
         ...
         [any_2 ..._1 ○ any_3 ...]
         [any_4 ..._1 ● any_5 ...]
         [any_6 ..._1 ● any_7 ...]
         any_8
         ...)
        (any_1
         ...
         [any_2 ... ● any_3 ...]
         [any_4 ... ○ any_5 ...]
         [any_6 ... ○ any_7 ...]
         any_8
         ...)
        ↑)))

;; every core is the same length for this winning? (only the peg count changes)
;; every move makes the same progress for board clearing...
;; ... meaning even the structure of the core doesn't help us
;; ways forward: strengthen phi? multiple phis? different smt query?
(define/debug (winning? board)
  (define/debug pegs-left-on-board
    (count (curry equal? '●) (flatten board)))
  (= pegs-left-on-board 1))

;; aha! we want to maximize being unstuck (ability to progress to satisfy winning?)
;; lots of ways to define unstuck, staying fairly propositionalized (more syntax more effect)
;; this is just defining winning as not losing, right?
#|
rosette hangs debugging this property

(define/debug (notlost? board)
  (define/debug (somestuck? r c board)
    (define/debug (pegless? r c board)
      (cond ((> r 0) (pegless? (- r 1) c (rest board)))
            ((= r 0) (pegless? (- r 1) c (first board)))
            ((> c 0) (pegless? r (- c 1) (rest board)))
            ((= c 0) (pegless? r (- c 1) (first board)))
            (else (not (equal? board '●)))))
    (define/debug (lonely? r c board)
      (and (pegless? (- r 1) c board)
           (pegless? (+ r 1) c board)
           (pegless? r (- c 1) board)
           (pegless? r (+ c 1) board)))
    (define/debug (stuck? r c board)
      (and (not (pegless? r c board)) (lonely? r c board)))
    (cond ((= r (length board)) (somestuck? 0 (+ c 1) board))
          ((= c (length (first board))) false)
          ((stuck? r c board) true)
          (else (somestuck? (+ r 1) c board))))
  (not (somestuck? 0 0 board)))
|#
(define (match-peg/neighbors board)
  (redex-match peg-solitaire
               (side-condition (any_1
                                ...
                                (position_1 ...            position_2   position_3 ...)
                                (position_4 ... position_5 peg          position_6 position_7 ...)
                                (position_8 ...            position_9   position_10 ...)
                                any_2
                                ...)
                               (and (= (length (term (position_1 ...)))
                                       (+ (length (term (position_4 ...))) 1)
                                       (length (term (position_8 ...))))
                                    (= (length (term (position_3 ...)))
                                       (+ 1 (length (term (position_7 ...))))
                                       (length (term (position_10 ...))))))
               board))
(define/debug (notlost? board)
  (define/debug (stuck? bindings)
    (define top (bind-exp (findf (lambda (abind) (equal? 'position_2 (bind-name abind))) bindings)))
    (define left (bind-exp (findf (lambda (abind) (equal? 'position_5 (bind-name abind))) bindings)))
    (define right (bind-exp (findf (lambda (abind) (equal? 'position_6 (bind-name abind))) bindings)))
    (define bot (bind-exp (findf (lambda (abind) (equal? 'position_9 (bind-name abind))) bindings)))
    (and
     (or (equal? top '○) (equal? top '█))
     (or (equal? left '○) (equal? left '█))
     (or (equal? right '○) (equal? right '█))
     (or (equal? bot '○) (equal? bot '█))))
  (define/debug (somestuck? matches)
    (cond ((empty? matches) false)
          (else (or (stuck? (match-bindings (first matches)))
                    (somestuck? (rest matches))))))
  (not (somestuck? (match-peg/neighbors board))))
                     
(define (search-for-solution board maximizing)
  (define (step move/board)
    (match-define `(,_ ,board) move/board)
    (define next-move/board
      (apply-reduction-relation/tag-with-names move board))
    (cond
      [(empty? next-move/board)
       (and (winning? board) `(,move/board))]
      [else
       (define (core phi t)
         (debug (boolean? integer?) (assert (phi t))))
       (define next-core/move/board
         (map (lambda (t) (cons (string-length (~a (core maximizing (second t)))) t))
              next-move/board))
       (define mincore (first (argmin first next-core/move/board)))
       (define nextmin-move/board
         (map rest
              (filter (lambda (t) (= mincore (first t))) next-core/move/board)))
       (define rest-of-solution
         (ormap step nextmin-move/board))
       (and rest-of-solution
            `(,move/board ,@rest-of-solution))]))
  (step `("initial" ,board)))
