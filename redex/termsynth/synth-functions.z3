;; UNIVERSE:
; there are terms
(declare-sort TERM)
; there is a distinct / fixed set (scalar sort) of types
(declare-datatypes () ((TYPE 
  NUMBER    
  STRING    
  T        
  F        
  UNDEFINED
  NULL
  NATURAL     
  REF      
  ERR      
  SET      
  ALLOC    
  DEREF    
  IF       
  BEGIN  
  )))

;; INTERPRETATION:
; a term has a type
(declare-fun typeof (TERM) TYPE)
; a term is a list of subterms
(declare-fun subterms (TERM (List TERM)) Bool)

;; ASSERT:
; number string #t #f undefined null natural
(assert (forall ((t TERM))
  (implies 
    (or 
      (= (typeof t) NUMBER)
      (= (typeof t) STRING)
      (= (typeof t) T)
      (= (typeof t) F)
      (= (typeof t) UNDEFINED)
      (= (typeof t) NULL)
      (= (typeof t) NATURAL))
    (subterms t nil)
    )))
; (ref natural)
(assert (forall ((t TERM)) 
  (implies 
    (= (typeof t) REF)
    (exists ((st1 TERM)) (and 
      (subterms t (insert st1 nil))
      (= (typeof st1) NATURAL)
      ))
    )))
; (err val)
; val := prim (ref natural)
; prim := number string #t #f undefined null
(assert (forall ((t TERM)) 
  (implies 
    (= (typeof t) ERR)
    (exists ((st1 TERM)) (and
      (subterms t (insert st1 nil))
      (or 
        (= (typeof st1) NUMBER)
        (= (typeof st1) STRING)
        (= (typeof st1) T)
        (= (typeof st1) F)
        (= (typeof st1) UNDEFINED)
        (= (typeof st1) NULL)
        (= (typeof st1) REF))
      ))
    )))
; (set! e e)
; (alloc e) 
; (deref e) 
; (if e e e)
; (begin e e ...))

;; QUERY:
; there is some term whose type is an expr
; e :=  number string #t #f undefined null
;       (ref natural) (err prim) (err (ref natural)) 
;       (set! e e) (alloc e) (deref e) (if e e e) (begin e e ...))

(check-sat)
(get-model)
