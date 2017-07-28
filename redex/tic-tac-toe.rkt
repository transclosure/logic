; Tic-tac-toe in Redex
; Modified only mildly by Tim Nelson 
; from Leandro Facchinetti's
; https://www.leafac.com/prose/playing-the-game-with-plt-redex/

#lang racket
(require redex)

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
1moves
(apply-reduction-relation move (first 1moves))

;(stepper move (term initial-board))

;(traces move (term initial-board))

; Alloy Way (pattern matching would be better)
(define (winning? board)
  (or (wins? board 'O)
      (wins? board 'X)))
(define (wins? board sym)
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

(search-for-solution (term initial-board))