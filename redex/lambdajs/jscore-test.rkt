#lang racket

(require redex)
(require "jscore.ss")
(require (rename-in "jscore-broken.ss"
                    (δ broken-δ)
                    (trace-errs-p broken-trace-errs-p)
                    (trace-errs broken-trace-errs)
                    (trace broken-trace)
                    (test broken-test)
                    (subst-vars broken-subst-vars)
                    (subst-n broken-subst-n)
                    (subst broken-subst)
                    (lambdaJS broken-lambdaJS)
                    (alloc-def broken-alloc-def)
                    (eval-lambdaJS-errors broken-eval-lambdaJS-errors)
                    (eval-lambdaJS broken-eval-lambdaJS)
                    ))

;; Without E-Break-Break, the term (label x (break y (break x 1))) gets stuck.
(define (success) (test (label x (break y (break x "success"))) "success"))
(define (failure) (broken-test (label x (break y (break x "success"))) "success"))

;; Without E-Break-Break, some term *should* get stuck (if we can find it)
;; Best redex functionality available: (redex-check template property-expr kw-arg ...)
;; optional kw-args may be helpful/harmful to redex search
;; template pattern for generating terms may be helpful/harmful to redex search

(define (value? t) (redex-match? broken-lambdaJS val t))
;; redex quickly finds missing Err-Break-Reduction/Err-Break-No-Label rule, using fixed error-eval
(define (reduces? t) (not (empty? (apply-reduction-relation eval-lambdaJS-errors t))))
;; had to start adding catches for "annoying" counterexamples
;; overconstraint is a big problem here!
(define (annoying? t) (or (redex-match? broken-lambdaJS variable-not-otherwise-mentioned t)
                          (redex-match? broken-lambdaJS (set! any_1 any_2) t)
                          (redex-match? broken-lambdaJS (alloc any_1) t)
                          (redex-match? broken-lambdaJS (deref any_1) t)
                          (redex-match? broken-lambdaJS (get-field any_1 any_2) t)
                          (redex-match? broken-lambdaJS (update-field any_1 any_2 any_3) t)
                          (redex-match? broken-lambdaJS (delete-field any_1 any_2) t)
                          (redex-match? broken-lambdaJS (throw any_1) t)
                          (redex-match? broken-lambdaJS (label variable-not-otherwise-mentioned_1
                                                               variable-not-otherwise-mentioned_2) t)
                          (redex-match? broken-lambdaJS (break variable-not-otherwise-mentioned_1
                                                               variable-not-otherwise-mentioned_2) t)
                          (redex-match? broken-lambdaJS (variable-not-otherwise-mentioned) t)
                          (redex-match? broken-lambdaJS (begin variable-not-otherwise-mentioned
                                                               any ...) t)
                          (redex-match? broken-lambdaJS (try-catch variable-not-otherwise-mentioned
                                                                   e) t)
                          (redex-match? broken-lambdaJS (try-finally variable-not-otherwise-mentioned
                                                                   e) t)
                          (redex-match? broken-lambdaJS (object (any_1
                                                                 any_2)) t)
                          (redex-match? broken-lambdaJS (variable-not-otherwise-mentioned val) t)
                          ))

(redex-check broken-lambdaJS e (or (value? (term e))
                                   (reduces? (term (() e)))
                                   (annoying? (term e)))
             #:prepare (lambda (t) (begin (printf "checking: ~a~n" t) t)))
