#lang rosette/safe

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
  ;TODO
  #|
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
|#
  (list ))
;;the free variables in a store.
(define (free-vars-store store)
  (apply append (map free-vars-expr (map second store))))
;;all object literals have unique names
(define (obj-unique-names-expr? expr)
  ;TODO
  #|
  (match expr
    [`(object [,str ,e] ...) (and (unique? str) (all (map obj-unique-names-expr? e)))]
    [`(,e ...) (all (map obj-unique-names-expr? e))]
    [else #t]))
|#
  #t)
(define (obj-unique-names-store? store)
  (all (map obj-unique-names-expr? (map second store))))
;;stuff to deal with refs being valid
(define ((collect-invalid-refs storedomain) expr)
  ;TODO
  #|
  (match expr
    [`(ref ,loc) (if (memq loc storedomain)
                     '()
                     (list loc))]
    [`(,e ...) (apply append (map (collect-invalid-refs storedomain) e))]
    [else '()]))
|#
  (list ))
;;all refs in an expression are in the domain of the store
(define ((valid-refs-expr? storedomain) expr)
  (= (length ((collect-invalid-refs storedomain) expr)) 0))
;;all refs in the store are in the domain of the store
(define (valid-refs-store? store)
  (all (map (valid-refs-expr? (map first store)) (map second store))))
;;stuff to deal with breaks being valid
(define ((collect-invalid-breaks curlabels) expr)
  ;TODO
  #|
  (match expr
    [`(break ,x ,e) (append (if (memq x curlabels) '() (list x))
                            ((collect-invalid-breaks curlabels) e))]
    [`(label ,x ,e) ((collect-invalid-breaks (cons x curlabels)) e)]
    ;;can't break across lambdas:
    [`(lambda (,x ...) ,e) ((collect-invalid-breaks '()) e)]
    [`(,e ...) (apply append (map (collect-invalid-breaks curlabels) e))]
    [else '()]
    ))
|#
  (list ))
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
Pure Redex Testing
|#
(define num-wellformed-inputs 0)
(define (safety-debug? p)
  (define (result? p)
    (or (redex-match lambdaJS error p)
        (redex-match lambdaJS val (second p))))
  (if (not (well-formed? p))
      #t ;;vacuously true
      (begin
        ;(print p) (display "\n")
        (set! num-wellformed-inputs (+ num-wellformed-inputs 1))
        (or (result? p) ;;either a result, or it reduces in 1 way to a well-formed result
            (let ((results (apply-reduction-relation eval-lambdaJS-errors p)))
              (and (= (length results) 1)
                   (well-formed? (first results))))))))
(define (redex-test attempts repeats)
  (if (<= repeats 0) void
      (begin
        (set! num-wellformed-inputs 0)
        (check-reduction-relation eval-lambdaJS-errors safety-debug? #:attempts attempts)
        (display (format "Repeat -~a: Had ~a/~a well-formed inputs\n" 
                         repeats num-wellformed-inputs (* 37 attempts)))
        (redex-test (+ attempts 1) (- repeats 1)))))
;(redex-test 1 10)

#|
SMT / Redex Testing
|#
;; universe of termposition(int)->isconcretetype?(bool) functions with grammatical interpretations
;; TODO not hardcoded language
(define (rosette-test)
  ; settings
  (current-bitwidth #f)
  (clear-asserts!)
  ; generic interpretation of (,)
  (define-symbolic openparen? (~> integer? boolean?))
  (define-symbolic closeparen? (~> integer? boolean?))
  ; generic interpretation of ... (variable size of 3)
  (define (a/k-listof? a/k-t? i)
    (define-symbolic* k-listof integer?)
    (define openparen1 (openparen? i))
    (define a/k-t1 (a/k-t? (+ i 1)))
    (define a-t1 (car a/k-t1))
    (define k-t1 (cdr a/k-t1))
    (define closeparen1 (closeparen? (+ i 1 k-t1)))
    (define k-listof1 (= k-listof (+ 1 k-t1 1)))
    (define openparen2 (openparen? (+ i 1 k-t1 1)))
    (define a/k-t2 (a/k-t? (+ i 1 k-t1 1 1)))
    (define a-t2 (car a/k-t2))
    (define k-t2 (cdr a/k-t2))
    (define closeparen2 (closeparen? (+ i 1 k-t1 1 1 k-t2)))
    (define k-listof2 (= k-listof (+ 1 k-t1 1 1 k-t2 1)))
    (define openparen3 (openparen? (+ i 1 k-t1 1 1 k-t2 1)))
    (define a/k-t3 (a/k-t? (+ i 1 k-t1 1 1 k-t2 1 1)))
    (define a-t3 (car a/k-t3))
    (define k-t3 (cdr a/k-t3))
    (define closeparen3 (closeparen? (+ i 1 k-t1 1 1 k-t2 1 1 k-t3)))
    (define k-listof3 (= k-listof (+ 1 k-t1 1 1 k-t2 1 1 k-t3 1)))
    (cons (or (and openparen1
                   a-t1
                   closeparen1
                   k-listof1)
              (and openparen1
                   a-t1
                   closeparen1
                   openparen2
                   a-t2
                   closeparen2
                   k-listof2)
              (and openparen1
                   a-t1
                   closeparen1
                   openparen2
                   a-t2
                   closeparen2
                   openparen3
                   a-t3
                   closeparen3
                   k-listof3))
          k-listof))
  ;(loc natural)
  (define-symbolic natural? (~> integer? boolean?))
  (define (a/k-loc? i)
    (define-symbolic k-loc integer?)
    (cons (and (natural? i)
               (= k-loc 1))
          k-loc))
  ;((val obj) prim (lambda (x ...) e) (ref loc) (object [string val] ...))
  ; TODO not concrete!!!!
  (define-symbolic val? (~> integer? boolean?)) 
  ;(σ ((loc val) ...))
  (define (a/k-loc.val? i)
    (define-symbolic* k-loc.val integer?)
    (cons (let* ((a/k-loc (a/k-loc? (+ i 1)))
                 (a-loc (car a/k-loc))
                 (k-loc (cdr a/k-loc)))
            (and (openparen? i)
                 a-loc
                 (val? (+ i 1 k-loc))
                 (closeparen? (+ i 1 k-loc 1))
                 (= k-loc.val (+ 1 k-loc 1 1))))
          k-loc.val))
  (define (a/k-σ? i)
    (define-symbolic* k-σ integer?)
    (cons (let* ((a/k-listof-loc.val (a/k-listof? a/k-loc.val? (+ i 1)))
                 (a-listof-loc.val (car a/k-listof-loc.val))
                 (k-listof-loc.val (cdr a/k-listof-loc.val)))
            (and (openparen? i)
                 a-listof-loc.val
                 (closeparen? (+ i 1 k-listof-loc.val))
                 (= k-σ (+ 1 k-listof-loc.val 1))))
          k-σ))
  ;(prim number string #t #f undefined null)
  ;(prim+prim-object prim (object [string prim+prim-object] ...))
  ;(error (err val))
  ;(prim+prim-object+error prim+prim-object error)
  ;(prim+error prim error)
  ;(not-object loc prim (lambda (x ...) e) (ref loc))
  ;(not-string loc number #t #f undefined null (lambda (x ...) e) (ref loc) (object [string val] ...))
  ;(not-lambda loc prim (ref loc) (object [string val] ...))
  ;(not-ref loc prim (lambda (x ...) e) (object [string val] ...))
  ;(not-bool loc number string undefined null (lambda (x ...) e) (ref loc) (object [string val] ...))
  ;(op + string-+ 
  ;    % - * / === ==
  ;    < string-< 
  ;    & \| ^ ~ << >> >>>
  ;    to-integer to-uint-32 to-int-32
  ;    = 
  ;    typeof surface-typeof
  ;    prim->number prim->string prim->bool
  ;    has-own-prop?
  ;    prim?)
  ;(lbl x)
  ;(e val
  ;   error
  ;   x 
  ;   (op e ...)
  ;   (e e ...)
  ;   (let ([x e] ...) e)
  ;   (set! e e) 
  ;   (alloc e) 
  ;   (deref e) 
  ;   (object [string e] ...)
  ;   (get-field e e) 
  ;   (update-field e e e)
  ;   (delete-field e e)
  ;   (begin e e ...) 
  ;   (if e e e)
  ;   (while e e) 
  ;   (try-catch e (lambda (x) e))
  ;   (try-finally e e)
  ;   (throw e)
  ;   (label lbl e))
  ;   (break lbl e)
  ;((f g x y z) variable-not-otherwise-mentioned)
  (define (lift i term sol)
    (define (continue-lift v)
      (lift (+ i 1) (append term `(,v)) sol))
    (cond (((evaluate openparen? sol) i) (continue-lift '\())
          (((evaluate closeparen? sol) i) (continue-lift '\)))
          (((evaluate natural? sol) i) (continue-lift 'nat))
          (((evaluate val? sol) i) (continue-lift `val))
          (else term)))
  (define a/k-term (a/k-σ? 1))
  (define a-term (car a/k-term))
  (define k-term (cdr a/k-term))
  (define sol (solve (assert a-term)))
  (printf "~a~n" sol)
  (and (sat? sol) (lift 1 '() sol)))
(rosette-test)
