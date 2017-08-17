#lang rosette

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

;; redex doesnt have a function for gettings the terminals of a language?!
;; !!!there has to be a more direct term to bitvector approach based on the grammar ordering
(define terminals
  (list '█ '○ '●))
(define terminalw
  (+ 1 (integer-sqrt (length terminals))))
(define (terminal->bitvector t)
  (integer->bitvector (index-of terminals t) (bitvector terminalw)))
(define (bitvector->terminal b)
  (define tail (list-tail terminals (bitvector->natural b)))
  (and (not (empty? tail)) (first tail)))

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

;; should be a single bitvector, no?
;; need a way to generalize kleene* to bitvectors without losing list structure
;; or using hardcoded constants for a 7x7 board?
(define (board->bitvector p**)
  (apply concat (map terminal->bitvector (flatten p**))))
(define (b->b* b i)
  (define j (+ (- i terminalw) 1))
  (cond ((< j 0) empty)
        (else (cons (extract i j b) (b->b* b (- j 1))))))
(define (b*->p* b*)
  (map bitvector->terminal b*))
(define (p*->p** p* p**)
  (cond ((empty? p*) p**)
        (else (p*->p** (drop p* 7) (cons (reverse (take p* 7)) p**)))))
(define (bitvector->board b)
  (p*->p** (b*->p* (reverse (b->b* b (- (* (* 7 7) terminalw) 1)))) empty))

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
(define (match-peg/neighbors* board)
  (redex-match peg-solitaire
               (side-condition (any_1
                                ...
                                (pos_1 ...            pos_2            pos_3 ...)
                                (pos_4 ... pos_5 pos_0 pos_6 pos_7 ...)
                                (pos_8 ...            pos_9            pos_10 ...)
                                any_2
                                ...)
                               (and (= (length (term (pos_1 ...)))
                                       (+ (length (term (pos_4 ...))) 1)
                                       (length (term (pos_8 ...))))
                                    (= (length (term (pos_3 ...)))
                                       (+ 1 (length (term (pos_7 ...))))
                                       (length (term (pos_10 ...))))))
               board))
(define (peg/neighbors* board)
  (define matches (match-peg/neighbors* board))
  (map peg/neighbors matches))
(define (peg/neighbors match)
  (define bindings (match-bindings match))
  (define peg (bind-exp (findf (lambda (abind) (equal? 'pos_0 (bind-name abind))) bindings)))
  (define top (bind-exp (findf (lambda (abind) (equal? 'pos_2 (bind-name abind))) bindings)))
  (define left (bind-exp (findf (lambda (abind) (equal? 'pos_5 (bind-name abind))) bindings)))
  (define right (bind-exp (findf (lambda (abind) (equal? 'pos_6 (bind-name abind))) bindings)))
  (define bot (bind-exp (findf (lambda (abind) (equal? 'pos_9 (bind-name abind))) bindings)))
  (list peg top left right bot))

(define/debug (stuck? p/ns)
  (and
   (equal? (first p/ns) '●)
   (or (equal? (second p/ns) '○) (equal? (second p/ns) '█))
   (or (equal? (third p/ns) '○) (equal? (third p/ns) '█))
   (or (equal? (fourth p/ns) '○) (equal? (fourth p/ns) '█))
   (or (equal? (fifth p/ns) '○) (equal? (fifth p/ns) '█))))
(define/debug (lost? p/ns*)
  (ormap stuck? p/ns*))

;; synthesize a rewrite of the term such that phi no longer fails
;; minimize the edit distance between the boards (xor is close but order biased)
(define (rewrite-bitvector b phi?)
  (define-symbolic bprime (bitvector (* (* 7 7) terminalw)))
  (define sol (optimize #:minimize (list (bvxor b bprime))
                        #:guarantee (assert (phi? (bitvector->board bprime)))))
  (evaluate bprime sol))
(define (write-board phi?)
  (define newboard (a7x7board 1))
  (define sol (optimize #:minimize empty
                        #:guarantee (assert (phi? newboard))))
  (evaluate newboard sol))

(apply printf (cons "~n~a~n~a~n~a~n~a~n~a~n~a~n~a~n"
                    (bitvector->board (rewrite-bitvector (board->bitvector (term lost-board))
                                                         winning?))))
(apply printf (cons "~n~a~n~a~n~a~n~a~n~a~n~a~n~a~n"
                    (bitvector->board (rewrite-bitvector (board->bitvector (term won-board))
                                                         (lambda (b) (not (winning? b)))))))
(apply printf (cons "~n~a~n~a~n~a~n~a~n~a~n~a~n~a~n"
                    (write-board winning?)))
(apply printf (cons "~n~a~n~a~n~a~n~a~n~a~n~a~n~a~n"
                    (write-board (lambda (b) (not (winning? b))))))

#||||||||||||||||||||||||||
| Term Reduction Checking |
||||||||||||||||||||||||||#
;; all of this is currently obsolete!!!

(define (core phi board)
  (debug (boolean? integer?) (assert (phi (peg/neighbors* board)))))
(define (core-weight phi board)
  (with-handlers ((exn:fail? (lambda (e) -1)))
    (string-length (~a (core phi board)))))
  
(define (search-for-solution board avoiding?)
  (define (step board)
    (apply printf (cons "~n~a~n~a~n~a~n~a~n~a~n~a~n~a~n" board))
    (define (expand boards)
      (append* (map (lambda (b) (begin
                                  (define choices (apply-reduction-relation move b))
                                  (if (empty? choices) b choices)))
                    boards)))
    (define next-boards
      (expand (list board)))
    (define next-weight/boards
      (filter (lambda (w/b) (positive? (first w/b)))
              (map (lambda (b) (cons (core-weight avoiding? b) b))
                   next-boards)))
    (cond ((empty? next-weight/boards)
           (and (winning? board) (list board)))
          (else
           (define sorted-next-boards
             (map rest (sort next-weight/boards
                             (lambda (a b) (> (first a) (first b))))))
           (define (dfs boards)
             (cond ((empty? boards) false)
                   (else
                    (define next (step (first boards)))
                    (cond ((false? next) (dfs (rest boards)))
                          (else (cons board next))))))
           (dfs sorted-next-boards))))
  (step board))
