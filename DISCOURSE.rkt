#lang rosette
(require ocelot)
(require racket/format)
(provide declare-rel
         declare-sig
         declare-cmd
         THIS)

(define DISCOURSE (make-hash))
(struct RELATION (THIS SUPER BOUND))
(define (THIS r) (RELATION-THIS (hash-ref DISCOURSE r)))
(define (SUPER r) (RELATION-SUPER (hash-ref DISCOURSE r)))
(define (UNIV upperbound name)
  (build-list upperbound (lambda (i) (string->symbol (string-append name "$" (~a i))))))
(define (UNIV* r)
  (let* ([SUPER (SUPER r)])
    (if (string? SUPER) (UNIV* SUPER) SUPER)))
(define (BOUND r) (RELATION-BOUND (hash-ref DISCOURSE r)))

(define (declare-rel parent arity name)
  (let* ([THIS (declare-relation arity name)]
         [SUPER parent]
         [U (UNIV* SUPER)]
         [BOUND (case arity
                  [(2) (make-product-bound THIS U U)]
                  [else (error "unsupported")])]
         [R (RELATION THIS SUPER BOUND)])
    (hash-set! DISCOURSE name R)))

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

(define (declare-cmd ocelot solve/verify?)
  (let* ([U (universe
             (first
              (append
               (filter list? (hash-map DISCOURSE (lambda (name relation) (SUPER name)))))))]
         [B (bounds U (hash-map DISCOURSE
                                (lambda (name relation) (RELATION-BOUND relation))))]
         [I (instantiate-bounds B)]
         [rosette (interpret* ocelot I)]
         [cmd (assert rosette)]
         [res (if solve/verify? (solve cmd) (verify cmd))]) ;TODO pretty printer
    (if (unsat? res) res (interpretation->relations (evaluate I res)))))
