#lang racket

(require redex)
(require "jscore.ss")
(require (rename-in "jscore-broken.ss"
                    (δ BROKEN-δ)
                    (trace-errs-p BROKEN-trace-errs-p)
                    (trace-errs BROKEN-trace-errs)
                    (trace BROKEN-trace)
                    (test BROKEN-test)
                    (subst-vars BROKEN-subst-vars)
                    (subst-n BROKEN-subst-n)
                    (subst BROKEN-subst)
                    (lambdaJS BROKEN-lambdaJS)
                    (alloc-def BROKEN-alloc-def)
                    (eval-lambdaJS-errors BROKEN-eval-lambdaJS-errors)
                    (eval-lambdaJS BROKEN-eval-lambdaJS)
                    ))

#|
essence of javascript paper semantic bug
|#
;; Without E-Break-Break, the term (label x (break y (break x 1))) gets stuck.
(define (success) (test (label x (break y (break x "success"))) "success"))
(define (failure) (BROKEN-test (label x (break y (break x "success"))) "success"))

#|
soundness
|#
(define (sound? p)
  (or (not (well-formed? p))
      (result? p)
      (let ((results (apply-reduction-relation eval-lambdaJS-errors p)))
        (and (= (length results) 1)
             (well-formed? (first results))))))
;; reduced term is a result:
(define (result? p)
  (or (redex-match lambdaJS error p)
      (redex-match lambdaJS val (second p))))

#|
well-formedness
|#
(define (well-formed? p)
  (or (redex-match lambdaJS error p)
      (and (correct-syntax? (second p))
           (obj-unique-names? p)
           (not (open? p))
           (valid-refs? p)
           (unique? (map first (first p)))
           (valid-breaks? p)
           )))
;;program contains free vars:
(define (open? p)
  (not (= 0 (+ (length (free-vars-expr (second p)))
               (length (free-vars-store (first p)))))))
;;object lits have unique names
(define (obj-unique-names? p)
  (and (obj-unique-names-expr? (second p))
       (obj-unique-names-store? (first p))))
;;program contains valid refs
(define (valid-refs? p)
  (and ((valid-refs-expr? (map first (first p))) (second p))
       (valid-refs-store? (first p))))
;;program has good syntax
(define (correct-syntax? expr)
  (redex-match lambdaJS e expr))
;;program contains only valid breaks (breaks to labels within lambdas)
(define (valid-breaks? p)
  (and ((valid-breaks-expr? '()) (second p))
       (valid-breaks-store? (first p))))
;;does l contains unique elements
(define (unique? l)
  (if (or (empty? l)
          (= (length l) 1))
      #t
      (and (not (member (first l) (rest l)))
           (unique? (rest l)))))
;;check for free variables
(define (free-vars-expr expr)
  (match expr
    [(? symbol? id) (if (or (eq? id 'eval-semantic-bomb)
                            (eq? id 'undefined)
                            (eq? id 'null))
                        '() 
                        (list id))]
    [`(,(? λJS-operator? op) ,e ...) (apply append (map free-vars-expr e))]
    [`(set! ,e1 ,e2) (append (free-vars-expr e1) (free-vars-expr e2))]
    [`(alloc ,e) (free-vars-expr e)]
    [`(deref ,e) (free-vars-expr e)]
    [`(ref ,loc) '()]
    [`(object [,str ,e] ...) (apply append (map free-vars-expr e))]
    [`(get-field ,e1 ,e2)  (append (free-vars-expr e1) (free-vars-expr e2))]
    [`(update-field ,e1 ,e2 ,e3) (append (free-vars-expr e1) (free-vars-expr e2) (free-vars-expr e3))]
    [`(begin ,e1 ,e2 ...) (append (free-vars-expr e1) (apply append (map free-vars-expr e2)))]
    [`(if ,e1 ,e2 ,e3) (append (free-vars-expr e1) (free-vars-expr e2) (free-vars-expr e3))]
    [`(while ,e1 ,e2) (append (free-vars-expr e1) (free-vars-expr e2))]
    [`(label ,lbl ,e) (free-vars-expr e)]
    [`(break ,lbl ,e) (free-vars-expr e)]
    [`(try-catch ,e1 ,e2) (append (free-vars-expr e1) (free-vars-expr e2))]
    [`(try-finally ,e1 ,e2) (append (free-vars-expr e1) (free-vars-expr e2))]
    [`(throw ,e1) (free-vars-expr e1)]
    [`(let ([,x ,e1] ...) ,e2) (append (apply append (map free-vars-expr e1))
                                       (setsub (free-vars-expr e2) x))]
    [`(lambda (,x ...) ,e) (setsub (free-vars-expr e) x)]
    [`(err ,e) (free-vars-expr e)]
    [`(delete-field ,e1 ,e2) (append (free-vars-expr e1) (free-vars-expr e2))]
    [`(,e ...) (apply append (map free-vars-expr e))]
    [else '()]
    ))
;;the free variables in a store.
(define (free-vars-store store)
  (apply append (map free-vars-expr (map second store))))
;;all object literals have unique names
(define (obj-unique-names-expr? expr)
  (match expr
    [`(object [,str ,e] ...) (and (unique? str) (all (map obj-unique-names-expr? e)))]
    [`(,e ...) (all (map obj-unique-names-expr? e))]
    [else #t]))
(define (obj-unique-names-store? store)
  (all (map obj-unique-names-expr? (map second store))))
;;stuff to deal with refs being valid
(define ((collect-invalid-refs storedomain) expr)
  (match expr
    [`(ref ,loc) (if (memq loc storedomain)
                     '()
                     (list loc))]
    [`(,e ...) (apply append (map (collect-invalid-refs storedomain) e))]
    [else '()]))
;;all refs in an expression are in the domain of the store
(define ((valid-refs-expr? storedomain) expr)
  (= (length ((collect-invalid-refs storedomain) expr)) 0))
;;all refs in the store are in the domain of the store
(define (valid-refs-store? store)
  (all (map (valid-refs-expr? (map first store)) (map second store))))
;;stuff to deal with breaks being valid
(define ((collect-invalid-breaks curlabels) expr)
  (match expr
    [`(break ,x ,e) (append (if (memq x curlabels) '() (list x))
                            ((collect-invalid-breaks curlabels) e))]
    [`(label ,x ,e) ((collect-invalid-breaks (cons x curlabels)) e)]
    ;;can't break across lambdas:
    [`(lambda (,x ...) ,e) ((collect-invalid-breaks '()) e)]
    [`(,e ...) (apply append (map (collect-invalid-breaks curlabels) e))]
    [else '()]
    ))
;;all breaks in an expression are valid
(define ((valid-breaks-expr? curlabels) expr)
  (= (length ((collect-invalid-breaks curlabels) expr)) 0))
;;all breaks in the store are valid
(define (valid-breaks-store? store)
  (all (map (valid-breaks-expr? '()) (map second store))))
;;substitute a for b
(define (setsub a b)
  (if (empty? b) a
      (setsub (filter (lambda (x) (not (eq? x (first b)))) a) (rest b))))
;;is x an op in our language
(define (λJS-operator? x)
  (member x
          '(+ string-+ 
              % - * / === ==
              < string-< 
              & \| ^ ~ << >> >>>
              to-integer to-uint-32 to-int-32
              = 
              typeof surface-typeof
              prim->number prim->string prim->bool
              has-own-prop?
              print-string
              str-contains str-startswith str-length str-split-regexp str-split-strexp
              regexp-quote regexp-match
              obj-iterate-has-next? obj-iterate-next obj-iterate-key
              obj-delete obj-can-delete?
              math-sin math-cos math-log math-exp math-abs math-pow
              prim?)))
;;andmap basically
(define (all l)
  (foldl (lambda (x y) (and x y)) #t l))

#|
Testing 
|#
(redex-check BROKEN-lambdaJS e (sound? (term (() e)))
             #:prepare (lambda (t) (begin (printf "checking: ~a~n" t) t)))
