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
(require rosette/solver/smt/z3)

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
  ; constants
  (define-symbolic apos integer?)
  ; terms have 1.variable size depending on subterms 2. a single concrete type
  (define-symbolic sizeof (~> integer? integer?))
  (define-symbolic typeof (~> integer? integer?))
  (define Tnull 0)
  ; generic interpretation of ...
  (define Tlist 1)
  (define (pos1 p) (+ p 1))
  (define (pos2 p) (+ (pos1 p) (sizeof (pos1 p))))
  (define (pos3 p) (+ (pos2 p) (sizeof (pos2 p))))
  (define (listof? apos t?)
    (or
     ; size 0
     (and (= (typeof apos) Tlist)
          (= (sizeof apos) 1))
     ; size 1
     (and (= (typeof apos) Tlist)
          (t? (pos1 apos))
          (= (sizeof apos) (+ 1 (sizeof (pos1 apos)))))
     ; size 2
     (and (= (typeof apos) Tlist)
          (t? (pos1 apos))
          (t? (pos2 apos))
          (= (sizeof apos) (+ 1 (sizeof (pos1 apos))
                              (sizeof (pos2 apos)))))
     ; size 3
     (and (= (typeof apos) Tlist)
          (t? (pos1 apos))
          (t? (pos2 apos))
          (t? (pos3 apos))
          (= (sizeof apos) (+ 1 (sizeof (pos1 apos))
                              (sizeof (pos2 apos))
                              (sizeof (pos2 apos)))))))
  ;(loc natural)
  (define-symbolic loc? (~> integer? boolean?))
  (define Tnatural 2)
  (assert (forall (list apos)
                  (<=> (loc? apos)
                       (and (= (typeof apos) Tnatural)
                            (= (sizeof apos) 1)))))
  ;((val obj) prim (lambda (x ...) e) (ref loc) (object [string val] ...))
  ; TODO not concrete!!!!
  (define-symbolic val? (~> integer? boolean?))
  (define Tval 3)
  (assert (forall (list apos)
                  (<=> (val? apos)
                       (and (= (typeof apos) Tval)
                            (= (sizeof apos) 1)))))
  ;(σ ((loc val) ...))
  (define-symbolic loc.val? (~> integer? boolean?))
  (assert (forall (list apos)
                  (<=> (loc.val? apos)
                       (and (= (typeof apos) Tlist)
                            (loc? (pos1 apos))
                            (val? (pos2 apos))
                            (= (sizeof apos) (+ 1 (sizeof (pos1 apos))
                                                (sizeof (pos2 apos))))))))
  (define-symbolic σ? (~> integer? boolean?))
  (assert (forall (list apos)
                  (<=> (σ? apos)
                       (listof? apos loc.val?))))
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
  ; term interpretation
  (define rootpos 1)
  (assert (forall (list apos)
                  (<=> (< (sizeof rootpos) apos)
                       (= (typeof apos) Tnull))))
  (define (interpret-term)
    (define termpos '(1 2 3 4 5 6 7 8 9 10))
    (interpret (reverse (take termpos (sizeof rootpos))) '()))
  (define (interpret pstack term)
    (cond ((null? pstack) term)
          ((= (typeof (first pstack)) Tlist)  `(listof,(sizeof (first pstack))))
          ; (interpret (rest pstack) (cons (take term (sizeof (first pstack)))
          ;                                (drop term (sizeof (first pstack))))))
          ((= (typeof (first pstack)) Tnatural) (interpret (rest pstack) (cons 'natural term)))
          ((= (typeof (first pstack)) Tval) (interpret (rest pstack) (cons 'val term)))))
  ; query
  (define sol (solve (assert (loc? rootpos))))
  (printf "~a~n" sol)
  (and (sat? sol) (evaluate (interpret-term) sol))
  )
(rosette-test)
