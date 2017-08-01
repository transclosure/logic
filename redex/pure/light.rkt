; Traffic light (classic)
; Two ways to model: explicit and implicit "turns"

#lang racket
(require redex)

(define-language lights 
  [light ::= red
             yellow
             green]
  [intersection-implicit ::= (light light)]
  [direction ::= ns ew]
  [intersection-explicit ::= (light light direction)])

(define-term initial-state-implicit (red red))
(define-term initial-state-explicit (red red ns))
(redex-match? lights intersection (term initial-state-explicit))

; Implicit turns
(define transition-implicit
  (reduction-relation
   lights
   #:domain intersection-implicit
   (--> (green any_1) 
        (yellow any_1)
        y1)
   (--> (any_2 green) 
        (any_2 yellow)
        y2)
   (--> (yellow any_3) 
        (red any_3)
        r1)
   (--> (any_4 yellow) 
        (any_4 red)
        r2)
   (--> (red red) 
        (green red)
        g1)     
   (--> (red red) 
        (red green)
        g2)     
  ))

; Explicit turns
(define transition-explicit
  (reduction-relation
   lights
   #:domain intersection-explicit
   (--> (green  any_1 ns) 
        (yellow any_1 ns)
        y_ns)
   (--> (any_1 green  ew) 
        (any_1 yellow ew)
        y_ew)
   (--> (yellow any_1 ns) 
        (red    any_1 ns)
        r_ns)
   (--> (any_1 yellow ew) 
        (any_1 red    ew)
        r_ew)
   (--> (red red   ns) 
        (red green ew)
        g_ns)     
   (--> (red   red ew) 
        (green red ns)
        g_ew)     
  ))

(printf "Implicit states starting from~n")
(term initial-state-implicit)
(define e1 (apply-reduction-relation transition-implicit (term initial-state-implicit)))
e1
(define e2 (apply append (map (curry apply-reduction-relation transition-implicit) e1)))
e2
(define e3 (apply append (map (curry apply-reduction-relation transition-implicit) e2)))
e3
(define e4 (apply append (map (curry apply-reduction-relation transition-implicit) e3)))
e4
(traces transition-implicit (term initial-state-implicit))

; QUESTION: why 2 (red red) states? Are they not considered equal?
;    The cycle gets found in traces and stepper calls below...

;(traces transition-implicit (term initial-state-implicit))
;(stepper transition-implicit (term initial-state-implicit))

(printf "Explicit states starting from~n")
(term initial-state-explicit)
(define e1exp (apply-reduction-relation transition-explicit (term initial-state-explicit)))
e1exp
(define e2exp (apply append (map (curry apply-reduction-relation transition-explicit) e1exp)))
e2exp
(define e3exp (apply append (map (curry apply-reduction-relation transition-explicit) e2exp)))
e3exp
(define e4exp (apply append (map (curry apply-reduction-relation transition-explicit) e3exp)))
e4exp
(define e5exp (apply append (map (curry apply-reduction-relation transition-explicit) e4exp)))
e5exp
(define e6exp (apply append (map (curry apply-reduction-relation transition-explicit) e5exp)))
e6exp
;(traces transition-explicit (term initial-state-explicit))