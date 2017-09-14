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

