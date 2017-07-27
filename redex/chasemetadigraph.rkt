#lang racket

(require redex)
(provide )

#||||||||||||
| Discourse |
||||||||||||#
;; herbrand, not kodkod
(define-language L
  (MODEL ::= (BASE UNIV)) ; a Model consists of a Base and a Universe
  (BASE ::= (e ...))      ; a Base is a set of Elements
  (UNIV ::= (F ...))      ; a Universe is a set of Facts over the Base
  (F ::= (R e ...))       ; a Fact is a Relation over a subset of Elements
  (R ::= any)             ; a Relation is just a special name
  (e ::= variable)        ; a Element is just a special variable
  )
;(render-language L)
(define-term emptyM (() ()))
(define-term nonemptyM ((e_1 e_2 e_3) ((Node e_1) (Node e_2) (Node e_3))))

#|||||||||
| Theory |
|||||||||#
;; no compiler, so just digraph for now
(define digraph
  (reduction-relation
   L #:domain MODEL
   (--> (side-condition
         ((any_1 ...) (any_2 ...))
         (not (redex-match? L
                            ((any_1 ...) (any_2 ... (Node e_rhs) any_3 ...))
                            (term ((any_1 ...) (any_2 ...)))))
         )
        ((any_1 ... e_1) (any_2 ... (Node e_1)))
        "{fresh Node}"
        (fresh e_1)
        )
   (--> (side-condition
         ((any_1 ... e_lhs any_2 ...) (any_3 ...))
         (not (redex-match? L
                            ((any_1 ... e_lhs any_2 ...) (any_3 ... (Node e_rhs) any_4 ...))
                            (term ((any_1 ... e_lhs any_2 ...) (any_3 ...)))
                            ))
         )
        ((any_1 ... e_lhs any_2 ...) (any_3 ... (Node e_lhs)))
        "{reuse Node}"
        )
   ; edge constraint not correct (pattern matching permutations is hard / barely know redex)
   (--> (side-condition
         ((any_1 ...) (any_2 ... (Node e_x) any_3 ...))
         (not (redex-match? L
                            ((any_1 ...) (any_2 ... (Node e_x) any_3 ... (Edge e_x e_rhs) any_4 ...))
                            (term ((any_1 ...) (any_2 ... (Node e_x) any_3 ...)))
                            ))
         )
        ((any_1 ... e_1) (any_2 ... (Node e_x) any_3 ... (Node e_1) (Edge e_x e_1)))
        "{all x:Node | fresh y:Node | edge(x,y)}"
        (fresh e_1)
        )
   (--> (side-condition
         ((any_1 ...) (any_2 ... (Node e_x) any_3 ... (Node e_y) any_4 ...))
         (not (redex-match? L
                            ((any_1 ...) (any_2 ... (Node e_x) any_3 ... (Node e_y) any_4 ... (Edge e_x e_rhs) any_5 ...))
                            (term ((any_1 ...) (any_2 ... (Node e_x) any_3 ... (Node e_y) any_4 ...)))
                            ))
         )
        ((any_1 ...) (any_2 ... (Node e_x) any_3 ... (Node e_y) any_4 ... (Edge e_x e_y)))
        "{all x:Node | reuse y:Node | edge(x,y)}"
        )
   ))
;(reduction-R->pict digraph)
;(stepper digraph (term emptyM))
;(stepper digraph (term nonemptyM))

#|||||||||||||||||||
| Search Algorithm |
|||||||||||||||||||#
;; not even going to try yet
