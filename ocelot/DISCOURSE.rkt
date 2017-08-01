#lang rosette
(require ocelot)
(require racket/format)
(provide declare-rel
         declare-sig
         declare-cmd
         THIS
         <=>
         CARD)
;TODO type checking
;; User-defined
(struct RELATION (THIS SUPER BOUND))
(define (THIS r) (RELATION-THIS (hash-ref DISCOURSE r)))
(define (SUPER r) (RELATION-SUPER (hash-ref DISCOURSE r)))
(define (BOUND r) (RELATION-BOUND (hash-ref DISCOURSE r)))
;; Built-in
(define DISCOURSE (make-hash))
(define (UNIV upperbound name)
  (build-list upperbound (lambda (i) (string->symbol (string-append name "$" (~a i))))))
(define (UNIV* r)
  (let* ([SUPER (SUPER r)])
    (if (string? SUPER) (UNIV* SUPER) SUPER)))
(define (<=> a b) (and (=> a b) (=> b a)))
(define (CARD set) (-1))
;TODO should bounds be declared/instantiated here or in cmd?
(define (declare-sig exact? upperbound name [extends ""])
  (let* ([THIS (declare-relation 1 name)]
         [SUPER (case extends
                  [("") (UNIV upperbound name)]
                  [else extends])]
         [U (case extends
              [("") SUPER]
              ;TODO fix naive extended upper bounds
              [else (take (UNIV* SUPER) upperbound)])] 
         [BOUND (if exact? (make-exact-bound THIS (map list U))
                    (make-upper-bound THIS (map list U)))]
         [R (RELATION THIS SUPER BOUND)])
    (hash-set! DISCOURSE name R)))
(define (declare-rel parent arity name)
  (let* ([THIS (declare-relation arity name)]
         [SUPER parent]
         [U (UNIV* SUPER)]
         [BOUND (case arity
                  [(2) (make-product-bound THIS U U)]
                  [(3) (make-product-bound THIS U U U)]
                  [else (error "unsupported")])]
         [R (RELATION THIS SUPER BOUND)])
    (hash-set! DISCOURSE name R)))
(define (declare-cmd ocelot [query none])
  (let* ([U (first (append
                    (filter list? (hash-map DISCOURSE (lambda (name rel) (SUPER name))))))]
         [E (declare-relation 1 (string-append "EVAL(" (~a query) "):="))]
         [B (bounds (universe U)
                    (cons (make-upper-bound E (map list U))
                          (hash-map DISCOURSE (lambda (name rel) (RELATION-BOUND rel)))))]
         [I (instantiate-bounds B)]
         [rosette (interpret* (and ocelot (= E query)) I)]
         [cmd (assert rosette)]
         [res (solve cmd)])
    (begin 
      (if (unsat? res) res
          (interpretation->relations (evaluate I res))))))