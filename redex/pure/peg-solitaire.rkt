#lang rosette

(require redex)
(require rosette/query/debug)

(define-language peg-solitaire
  [position ::= █ ○ ●]
  [board ::= ([position ...] ...)])

(define-term initial-board
  ([█ █ ● ● ● █ █]
   [█ █ ● ● ● █ █]
   [● ● ● ● ● ● ●]
   [● ● ● ○ ● ● ●]
   [● ● ● ● ● ● ●]
   [█ █ ● ● ● █ █]
   [█ █ ● ● ● █ █]))

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

(define/debug (winning? board)
  (define pegs-left-on-board
    (count (curry equal? '●) (flatten board)))
  (= pegs-left-on-board 1))

(define (search-for-solution board)
  (define (core phi t)
    (debug (boolean? integer?) (assert (phi t))))
  (define (step move/board)
    (match-define `(,_ ,board) move/board)
    (define next-move/board
      (apply-reduction-relation/tag-with-names move board))
    (cond
      [(empty? next-move/board)
       (and (winning? board) `(,move/board))]
      [else
       (define next-core/move/board
         ;; every core is the same length for this phi! (only the peg count changes
         ;; every move makes the same progress for board clearing...
         ;; ... meaning even the structure of the core doesn't help us
         ;; ways forward: strengthen phi? multiple phis? different smt query?
         (map (lambda (t) (cons (string-length (~a (core winning? t))) t))
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
