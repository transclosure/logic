#lang rosette

(provide (all-defined-out))

; INSTRUCTION: this file must not be modified.

; Define a state to have A x l r ans
; A: a vectorof number
; x: a number (to search for)
; l: a number (left in the algorithm)
; r: a number (right in the algorithm)
; ans: an answer (the index, -1 if there is no x in A)

; You can create a state by writing (state <...> <...> <...> <...>)
; To refer to a field of a state, use (state-<field> <a state>)
; If a state is an input to a function, you can use a special form
; define-match to destruct and obtain fields in one go. See bsearch0.rkt
; for an example
(struct state (A x l r ans) #:transparent)