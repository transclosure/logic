#lang rosette

(provide (all-defined-out))

(current-bitwidth 8)

(define-match-expander ::
  (lambda (stx)
    (syntax-case stx ()
      [(_ f r)
       #'(? cons? (app (lambda (v) (values (first v) (rest v))) f r))]))
  (lambda (stx)
    (syntax-case stx ()
      [(_ f r)
       #'(cons f r)])))

(define-syntax-rule (while condition body ...)
  (let loop ()
    (cond [condition body ... (loop)] [else (void)])))

#|
(define vec-ref vector-ref)
(define-syntax vec-set!
  (syntax-rules ()
    [(_ a b c) (begin (set! a (vector-append a (vector)))
                      (vector-set! a b c))]))
(define (vec-slice->list a b c)
  (take (drop (vector->list a) b) (- c b)))
|#

(define space "")
(define (set-space! s) (set! space s))

(define debug-setting #f)
(define (set-debug! c) (set! debug-setting c))

(define-syntax ~
  (syntax-rules ()
    [(_ (sf sr ...) whatever ...)
     (printf (apply string-append (list (if debug-setting
                                            space
                                            "")
                                        sf
                                        sr ...))
             whatever ...)]))

(define-syntax define-match
  (syntax-rules ()
    [(_ (f pat) body ...)
     (define (f s) (match s [pat body ...]))]))

(define-syntax assert-scope
  (syntax-rules ()
    [(_ assertion whatever ...)
     (define-values (_ _2)
       (with-asserts
           (begin
             (set-space! (string-append "  " space))
             (when debug-setting
               (~ ["(begin a new scope)\n"]))
             (assert assertion)
             whatever ...
             (when debug-setting
               (~ ["(exit a scope)\n\n"]))
             (set-space! (substring space 2)))))]))
