; Traffic light (classic)
; Two ways to model: explicit and implicit "turns"
; Implicit: state only tracks light colors, and it is non-deterministic who goes from (red red).
; Explicit: state tracks light colors /and/ whose turn it is to go next.
;
; Safety property: always some light is red.
; Liveness property: neither direction is starved; each always eventually gets to go.
; Expect that both pass safety but implicit fails liveness. 

#lang rosette
(require redex)
(require rosette/query/debug
         rosette/lib/render)

(define-language lights 
  [light ::= red
         yellow
         green]
  [intersection-implicit ::= (light light)]
  [direction ::= ns ew]
  [intersection-explicit ::= (light light direction)])

(define-term initial-state-implicit (red red))
(define-term initial-state-explicit (red red ns))
; Test: terms work as expected?
(redex-match? lights intersection-explicit (term initial-state-explicit))
(redex-match? lights intersection-implicit (term initial-state-implicit))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
        g2)))

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
        g_ew)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Explore reachable states naively (more sanity checking of the "spec")

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
; Repeats are an artifact of search.

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
(define e7exp (apply append (map (curry apply-reduction-relation transition-explicit) e6exp)))
e7exp
;(traces transition-explicit (term initial-state-explicit))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Property verification!

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Safety: always some red light
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test-->> isn't quite what we want, because it implicitly calls apply-reduction-relation* w/o "all?" set.
; Without that option it'l only return terms that don't reduce. Instead:

(define reachable-explicit (apply-reduction-relation* #:all? #t #:cache-all? #t transition-explicit (term initial-state-explicit)))
(define reachable-implicit (apply-reduction-relation* #:all? #t #:cache-all? #t transition-implicit (term initial-state-implicit)))
; ^ note that this is only checking for reachability from START. 

; Check safety: every reachable state has >=1 light red:
(define/debug (unsafe? t)
  (not (or (symbol=? (first t) 'red)
           (symbol=? (second t) 'red))))

(define (safety reachable)
  (not (ormap unsafe? reachable)))

(define (core phi t)
  (assert (phi t)))

(define (cores property reachable)
  (map (lambda (t) (printf "~n~a~n~a~n" t (debug (boolean?) (core property t))))
       reachable))

(cores unsafe? reachable-implicit)

(printf "Implicit safety (true means pass): ~a~n" (safety reachable-implicit))
(printf "Explicit safety (true means pass): ~a~n" (safety reachable-explicit))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Liveness: non-starvation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; For each reachable state, does AFgreen hold?
; (Inefficient search using apply-reduction-relation, not a CTL model checker!)


; afphi returns #f if there is no counterexample starting from this state. 
; otherwise: returns a path that falsifies the property
(define (afphi visited phi? tr s) 
  (define nextss (apply-reduction-relation tr s))         
  (cond
    ; If this state satisfies phi, suffices (slow positioning, could move up)
    [(phi? s) #f]
    ; No next states but does not satisfy phi
    [(empty? nextss) visited]           
    [else
     ; If a child state meets phi, no need to check it.
     ; If we find a cycle of unmet-phi states, fail.
     (define obligations (filter (lambda (n) (not (phi? n))) nextss))
     (cond [(check-duplicates (append obligations visited))
            visited]
           [else
            (ormap (curry afphi (cons s visited) phi? tr) obligations)])]))

(define (liveness-helper curried-afphi reachable)
  (ormap (lambda (s)
           (define result (curried-afphi s))
           ; Here is where we'd add the path to s if we had it.
           (cond [(list? result) result]
                 [else #f])) reachable))

; Check east-west liveness. Handwaving north-south via symmetry.
(define liveness-implicit
  (liveness-helper
   (curry afphi
          empty
          ; A state satisfies phi if the east-west light is green
          (lambda (s) (equal? s '(red green)))
          transition-implicit)
   reachable-implicit))

; Check east-west liveness. Handwaving north-south via symmetry.
(define liveness-explicit
  (liveness-helper
   (curry afphi
          empty
          ; A state satisfies phi if the east-west light is green
          (lambda (s) (or (equal? s '(red green ew))))
          transition-explicit)
   reachable-explicit))

; Observation: it's a bit tougher to sanity check the above than it is in Alloy,
; since I'm not just writing a spec---I'm writing a very dumb model checker!

(printf "Implicit liveness (false means pass): ~a~n" liveness-implicit)
(printf "Explicit liveness (false means pass): ~a~n" liveness-explicit)

#||||||||||||||||||||||||||
| SVM-eqsue State Merging |
||||||||||||||||||||||||||#
;; original state machine
(define SM (traces transition-implicit (term initial-state-implicit)))
;; added formulae
#|
b1 = g1 | g2
i1 = green | red
i2 = red | green
b1 = g1 ===> i1 = green & i2 = red
b1 = g2 ===> i1 = red & i2 = green
b2 = y1 | y2
i3 = yellow | i1
i4 = i2 | yellow
b2 = y1 ===> i3 = yellow & i4 = i2
b2 = y2 ===> i3 = i1 & i4 = yellow
b3 = r1 | r2
i5 = red | i3
i6 = i4 | red
b3 = r1 ===> i5 = red & i6 = i4
b3 = r2 ===> i5 = i3 & i6 = red
|#
;; merged state machine
#|
(red red)
   g1 -> (green red), g2 -> (red green)
b1 -> (i1 i2)
   y1 -> (yellow i2), y2 -> (i1 yellow)
b2 -> (i3 i4)
   r1 -> (red i4), r2 -> (i3 red)
b3 -> (i5 i6)
|#
