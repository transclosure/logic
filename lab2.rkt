#lang rosette
(require ocelot)

; Universe of Discourse
(require "DISCOURSE.rkt")
(declare-sig #f 4 "Memory")
(declare-sig #f 4 "HeapCell" "Memory")
(declare-sig #t 1 "Stack" "Memory")
(declare-sig #f 3 "State")
(declare-rel "State" 2 "allocated")
(declare-rel "State" 3 "references")
(declare-sig #t 1 "StateA")
(declare-sig #t 1 "StateB")
(declare-sig #t 1 "StateC")
; Functions / Predicates / Asserts
(define (REFCOUNT state cell)
  (join (join state (THIS "references")) cell))
(define (STKREACH state cell)
  (in cell (join (THIS "Stack")
                 (^ (join state (THIS "references"))))))
(define (SAFE state)
  (all ([cell (THIS "HeapCell")])
       (=> (STKREACH state cell)
           (in cell (join state (THIS "allocated"))))))
(define (CLEAN state)
  (all ([cell (THIS "HeapCell")])
       (=> (in cell (join state (THIS "allocated")))
           (STKREACH state cell))))
; Facts
(define fUnallocatedCantReference
  (all ([state (THIS "State")]
        [cell (- (THIS "HeapCell")
                 (join state (THIS "allocated")))])
       (no (join state (join cell (THIS "references"))))))
(define fAllocatedUnchanged
  (= (join (THIS "StateA") (THIS "allocated"))
     (join (THIS "StateB") (THIS "allocated"))))
(define fGarbageCollection
  (and (= (join (THIS "StateB") (THIS "references"))
          (join (THIS "StateC") (THIS "references")))
       (all ([cell (THIS "HeapCell")])
            (<=> (not (in cell (join (THIS "StateC")
                                     (THIS "allocated"))))
                 (= (REFCOUNT (THIS "StateB") cell) 0)))))  
; Models
(define (verifySOUNDNESS [query none])
  (declare-cmd (and fUnallocatedCantReference
                    fAllocatedUnchanged
                    fGarbageCollection
                    (SAFE (THIS "StateA"))
                    (not (SAFE (THIS "StateC"))))
               query))
(verifySOUNDNESS)
