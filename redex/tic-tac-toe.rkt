; Tic-tac-toe in Redex
; Modified only mildly by Tim Nelson 
; from Leandro Facchinetti's
; https://www.leafac.com/prose/playing-the-game-with-plt-redex/

#lang rosette
(require redex)
(require rosette/query/debug
         rosette/lib/render)

(define-language tic-tac-toe
  [position ::= █ X O]
  [turn ::= X O]
  [board ::= (turn [position ...] ...)])

(define-term initial-board
  (X
   [█ █ █]
   [█ █ █]   
   [█ █ █]))

; Easier by far than solitare because tic-tac-toe is context-insensitive: see an empty position, can fill it
; (Recall the any ... idiom is *, not +)
(define move
  (reduction-relation
   tic-tac-toe
   #:domain board
   (--> (O
         any_1
         ...
         [any_2 ... █ any_3 ...]
         any_4
         ...)
        (X
         any_1
         ...
         [any_2 ... O any_3 ...]
         any_4
         ...)
        o-move)
   (--> (X
         any_1
         ...
         [any_2 ... █ any_3 ...]
         any_4
         ...)
        (O
         any_1
         ...
         [any_2 ... X any_3 ...]
         any_4
         ...)
        x-move)))

(define 1moves (apply-reduction-relation move (term initial-board)))
;(apply-reduction-relation move (first 1moves))
;(stepper move (term initial-board))
;(traces move (term initial-board))

(define (printboard board)
  (printf "~n~s~n~s~n~s~n" (first board) (second board) (third board)))
(define (printmove move)
  (define board (rest (second move)))
  (printboard board)
  (printf "~a move, gives control to ~a~n" (first move) (first (second move)))
  )

; Alloy Way (pattern matching would be better)
(define/debug (wins? board sym)
  (define row1 (second board))
  (define row2 (third board))
  (define row3 (fourth board))
  (or
   ; win horizontally
   (equal? row1 (list sym sym sym))
   (equal? row2  (list sym sym sym))
   (equal? row3 (list sym sym sym))
   ; win vertically
   (and (equal? (first row1) sym)
        (equal? (first row2) sym)
        (equal? (first row3) sym))
   (and (equal? (second row1) sym)
        (equal? (second row2) sym)
        (equal? (second row3) sym))
   (and (equal? (third row1) sym)
        (equal? (third row2) sym)
        (equal? (third row3) sym))   
   ; win diagonally
   (and (equal? (first  row1) sym)
        (equal? (second row2) sym)
        (equal? (third  row3) sym))
   (and (equal? (third  row1) sym)
        (equal? (second row2) sym)
        (equal? (first  row3) sym))))

(define/debug (owins? board) (wins? board 'O))
(define/debug (xwins? board) (wins? board 'X))
(define/debug (winning? board) (or (owins? board) (xwins? board)))

(define (core phi t) (debug (boolean?) (assert (phi t))))
(define (cores property reachable)
  (for-each (lambda (t)
              (begin (printboard (rest t))
                     (printf "[corelen=~a]~n"
                             (string-length (~a (core property t))))))
            reachable))

(define reach1 (apply-reduction-relation move (term initial-board)))
(define reach2 (append* (map (lambda (b) (apply-reduction-relation move b)) reach1)))
(define reach3 (append* (map (lambda (b) (apply-reduction-relation move b)) reach2))) 
;(cores xwins? reach3)

; Almost verbatim from blog -- but no need to hit final state to win
; Naive BFS. 
(define (search-for-solution board)
  (define (step board-with-move)
    (match-define `(,_ ,board) board-with-move)
    (define next-boards-with-moves
      (apply-reduction-relation/tag-with-names move board))
    (cond
      [(winning? board) `(,board-with-move)]
      [else
       (define rest-of-solution
         (ormap step next-boards-with-moves))
       (and rest-of-solution
            `(,board-with-move ,@rest-of-solution))]))
  (step `("initial" ,board)))

(define soln (search-for-solution (term initial-board)))
;(for-each printmove soln)
;(cores xwins? (map (lambda (move) (second move)) soln))

(define (search-for-solution/min-core board phi?)
  (define (step board-with-move)
    (match-define `(,_ ,board) board-with-move)
    (define next-boards-with-moves
      (apply-reduction-relation/tag-with-names move board))
    (define next-boards-with-moves/cores
      (map (lambda (board-with-move)
             (cons (string-length (~a (core phi? (rest (second board-with-move)))))
                   board-with-move))
           next-boards-with-moves))
    (define next-board-with-move/min-core
      (cond
        ((empty? next-boards-with-moves/cores) empty)
        (else (rest (argmin first next-boards-with-moves/cores)))))
    (cond
      [(phi? board) `(,board-with-move)]
      [(empty? next-board-with-move/min-core) `(,board-with-move)]
      [else
       (define rest-of-solution (step next-board-with-move/min-core))
       (and rest-of-solution
            `(,board-with-move ,@rest-of-solution))]))
  (step `("initial" ,board)))

(for-each printmove (search-for-solution/min-core (term initial-board) xwins?))
