#lang racket
(require redex)

;; Syntax
(define-language kodkod
  [problem ::= ((relDecl ...) formula)]
  [relDecl ::= (rel arity constant constant)]
  [varDecl ::= (var expr)]
  [binding ::= (rel constant) (var constant)]
  [constant ::= (tuple ...)]
  [tuple ::= (atom ...)]
  [arity   ::= number]
  [atom    ::= variable]
  [rel     ::= variable]
  [var     ::= variable]
  [expr    ::= rel var unary binary compreh]
  [unary   ::= (unop expr)]
  [unop    ::= ~ ^]
  [binary  ::= (binop expr expr)]
  [binop   ::= + & - dot ->]
  [compreh ::= (varDecl formula)]
  [formula ::= elementary composite quantified]
  [elementary ::= (in expr expr) (mult expr)]
  [mult ::= some no one]
  [composite ::= (not formula) (logop formula formula)]
  [logop ::= and or]
  [quantified ::= (quantifier varDecl formula)]
  [quantifier ::= all some]
  #:binding-forms
  (((rel arity constant constant) ...) formula #:refers-to (shadow rel ...))
  )
(define-language solver [command ::= any])

;; Semantics
(define-union-language naive-encoding (kodkod. kodkod) (solver. solver))
(define-metafunction naive-encoding
  P : kodkod.problem (kodkod.binding ...) -> solver.command
  [(P ((kodkod.relDecl_1 ...) kodkod.formula_1)
      (kodkod.binding_1 ...))
   (M kodkod.formula_1
      (kodkod.binding_1 ... (R kodkod.relDecl_1) ...))]
  )
(define-metafunction naive-encoding
  R : kodkod.relDecl -> kodkod.binding
  [(R (kodkod.rel_1 kodkod.arity_1 kodkod.constant_1 kodkod.constant_2))
   (kodkod.rel_1 kodkod.constant_2)]
  )
(define-metafunction naive-encoding
  M : kodkod.formula (kodkod.binding ...) -> solver.command
  [(M (in kodkod.expr_1 kodkod.expr_2) (kodkod.binding_1 ...))
   (subsetof (X kodkod.expr_1 (kodkod.binding_1 ...)) (X kodkod.expr_2 (kodkod.binding_1 ...)))]
  [(M (some kodkod.expr_1) (kodkod.binding_1 ...))
   (subsetof emptyset (X kodkod.expr_1 (kodkod.binding_1 ...)))]
  [(M (one kodkod.expr_1) (kodkod.binding_1 ...))
   (equal (sizeof (X kodkod.expr_1 (kodkod.binding_1 ...))))]
  [(M (no kodkod.expr_1) (kodkod.binding_1 ...))
   (subsetof (X kodkod.expr_1 (kodkod.binding_1 ...)) emptyset)]
  [(M (not kodkod.formula_1) (kodkod.binding_1 ...))
   (not (M kodkod.formula (kodkod.binding_1 ...)))]
  [(M (and kodkod.formula_1 kodkod.formula_2) (kodkod.binding_1 ...))
   (and (M kodkod.formula_1 (kodkod.binding_1 ...)) (M kodkod.formula_2 (kodkod.binding_1 ...)))]
  [(M (or kodkod.formula_1 kodkod.formula_2) (kodkod.binding_1 ...))
   (or (M kodkod.formula_1 (kodkod.binding_1 ...)) (M kodkod.formula_2 (kodkod.binding_1 ...)))]
  [(M (all (kodkod.var_1 kodkod.expr_1) kodkod.formula_1) (kodkod.binding_1 ...))
   (and (M kodkod.formula_1 (kodkod.binding_1 ...)))]
  [(M (some (kodkod.var_1 kodkod.expr_1) kodkod.formula_1) (kodkod.binding_1 ...))
   (bigor-foreachbinding (M kodkod.formula_1 (kodkod.binding_1 ...)))]
  )
(define-metafunction naive-encoding
  X : kodkod.expr (kodkod.binding ...) -> kodkod.binding
  [(X _ any) any]
  )
(define naive-encoding-reduction
  (reduction-relation naive-encoding
   (--> kodkod.problem_1 (P kodkod.problem_1 ()) encode)))

;; Examples
(define-term kodkod-digraph (((Node 1 () ((N1) (N2)))
                       (edge 2 () ((N1 N1) (N1 N2) (N2 N1) (N2 N2))))
                      (all (n Node) (some (e edge) (in e (dot n edge))))
                      ))

(traces naive-encoding-reduction (term kodkod-digraph))
