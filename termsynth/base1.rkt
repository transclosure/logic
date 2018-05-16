#lang racket
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Smaller subset of lambda JS core
; Still involves heaps, errors, etc.
; Uses evaluation contexts and 1 metafunction.
; Does not yet require the js-delta file.
; TN
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(require redex)
;(require "../lambdajs/js-delta.ss")
(provide (all-defined-out))

(define-language lambdaJS
  (σ ((loc val) ...))                          ; a heap
  (loc natural)                                ; a heap location
  (prim number string #t #f undefined null)    ; primitives: nums, strs, bools, undef, null
  (val prim (ref loc))                         ; a VALUE is a primitive or a heap reference
  (error (err val))                            ; an error

  ; For malformed "if" error
  (not-bool loc number string undefined null (ref loc))
  ; For malformed set! etc.
  ; NOTE: if this non-term is left out, don't get an error when we refer to it in transition function.
  ;     Q: Is this because then it's just a symbol to match exactly?
  (not-ref loc prim)

  ; Expressions
  (e val
     error
     ;x  ; Ignore "x" for now
     (set! e e) 
     (alloc e) 
     (deref e) 
     (if e e e)
     (begin e e ...)
     )
 
  (E hole 
     (val ... E e ...)
     (alloc E)
     (deref E)
     (set! E e) (set! val E)
     (begin val ... E e ...)
     (if E e e)
     )
  ; E and F are the same for this sublanguage
  (F hole 
     (val ... F e ...)
     (alloc F)
     (deref F)
     (set! F e) (set! val F)
     (begin val ... F e ...)
     (if F e e))
  )

; One metafunction: allocating onto the heap

(define-metafunction lambdaJS
  alloc-def : val σ -> (loc σ)
  [(alloc-def val_new ((loc val) ...))
   ,(term-let ([loc_new (+ 1 (apply max (term (0 loc ...))))])
              (term (loc_new ((loc_new val_new) (loc val) ...))))])

;;----------------------------------------
;;error-free relation:
(define eval-lambdaJS
  (reduction-relation
   lambdaJS
   (--> (((loc_1 val_1) ... (loc val_old) (loc_3 val_3) ...) 
         (in-hole E (set! (ref loc) val_new)))
        (((loc_1 val_1) ... (loc val_new) (loc_3 val_3) ...) 
         (in-hole E (ref loc)))
        "E-Assign")
   
   (--> (σ_1 (in-hole E (alloc val)))
        (σ_2 (in-hole E (ref loc)))
        "E-Alloc"
        (where (loc σ_2) (alloc-def val σ_1)))
   (--> (((loc_1 val_1) ... (loc_2 val_2) (loc_3 val_3) ...) (in-hole E (deref (ref loc_2))))
        (((loc_1 val_1) ... (loc_2 val_2) (loc_3 val_3) ...) (in-hole E val_2))
        "E-Deref")

   ; Fun demo of evaluation contexts working: without E, this wouldn't suffice
   (==> (begin val ... val_r)
        val_r
        "E-BeginResult")
   
   (==> (if #t e_1 e_2)
        e_1
        "E-IfTrue")
   (==> (if #f e_1 e_2)
        e_2
        "E-IfFalse")

   ; Need this to address error sub-terms and let them reduce by bubbling up
   (--> (σ (in-hole F (err val)))
        (err val)
        "E-Throw-Uncaught")
   
   with
   [(--> (σ (in-hole E expr1)) (σ (in-hole E expr2)))
    (==> expr1 expr2)]))

;;----------------------------------------
;;error reductions:
(define eval-lambdaJS-errors
  (extend-reduction-relation 
   eval-lambdaJS
   lambdaJS
   (--> (((loc_1 val_1) ... ) 
         (in-hole E (set! (ref loc) val_new)))
        (err "Setting invalid ref")
        (side-condition (not (memq (term loc) (term (loc_1 ...)))))
        "E-Assign-NotFound")
   (==> (set! not-ref val)
        (err "Setting a not-ref")
        "E-Assign-NotRef")
   
   (--> (((loc_1 val_1) ...) (in-hole E (deref (ref loc))))
        (err "deref of an invalid location")
        (side-condition (not (memq (term loc) (term (loc_1 ...)))))
        "E-Deref-NotFound")
   (==> (deref not-ref)
        (err "deref of a not-ref")
        "E-Deref-NotRef")
  
   (==> (if not-bool e_1 e_2)
        (err "if not given a boolean test")
        "E-If-NotBool")
   
   with
   [(--> (σ (in-hole E expr1)) (σ (in-hole E expr2)))
    (==> expr1 expr2)]
   ))

