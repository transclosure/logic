#lang rosette
#|||||||||||||||||||||||||||||||||||||||
| Alloy Compiler for Ocelot/Rosette/Z3 |
|||||||||||||||||||||||||||||||||||||||#
;; mandatory
(require ocelot)
(require redex/reduction-semantics)
;; optional
(require redex/pict)
(require redex/gui)
#|||||||||
| Syntax |
|||||||||#
;; Adapted from http://alloy.mit.edu/alloy/documentation/alloy4-grammar.txt
(define-language ALLOY
  (pSPEC ::= pALLOY pOCELOT)
  (pOCELOT ::= string) ;TODO hook ocelot syntax tree
  ;; specification ::= [module] open* paragraph*
  (pALLOY ::= (pPar ...+))
  ;; module ::= "module" name  [ "["  ["exactly"] name  ("," ["exactly"] num)*    "]" ]
  ;TODO
  ;; open ::= ["private"]  "open"  name  [ "[" ref,+ "]" ]  [ "as" name ]
  ;TODO
  ;; paragraph ::= factDecl | assertDecl | funDecl | cmdDecl | enumDecl | sigDecl
  (pPar ::= pFact pFunc pCmd pSig)
  ;; factDecl ::= "fact" [name] block
  (pFact ::= (fact pName pBlock))
  ;; assertDecl ::= "assert" [name] block
  ;TODO
  ;; funDecl ::= ["private"] "fun" [ref "."] name "(" decl,* ")" ":" expr block
  ;; funDecl ::= ["private"] "fun" [ref "."] name "[" decl,* "]" ":" expr block
  ;; funDecl ::= ["private"] "fun" [ref "."] name                ":" expr block
  ;; funDecl ::= ["private"] "pred" [ref "."] name "(" decl,* ")" block
  ;; funDecl ::= ["private"] "pred" [ref "."] name "[" decl,* "]" block
  ;; funDecl ::= ["private"] "pred" [ref "."] name                block
  (pFunc ::= (func pName (pDecl ...) pExpr pBlock))
  ;; cmdDecl ::= [name ":"] ("run"|"check") (name|block) scope
  (pCmd ::= (cmd pName pBlock pScope))
  ;; scope ::= "for" number                   ["expect" (0|1)]
  ;; scope ::= "for" number "but" typescope,+ ["expect" (0|1)]
  ;; scope ::= "for"              typescope,+ ["expect" (0|1)]
  ;; scope ::=                                ["expect" (0|1)]
  (pScope ::= (for integer (pScopeT ...)))
  ;; typescope ::= ["exactly"] number [name|"int"|"seq"]
  (pScopeT ::= (exactly integer pName) (integer pName))
  ;; enumDecl ::= "enum" name "{" name  ("," name)*  "}"
  ;TODO
  ;; sigDecl ::= sigQual* "sig" name,+ [sigExt] "{" decl,* "}" [block]
  (pSig ::= (sig (pSigQ ...) (pName ...+) pSigX pBlock))
  ;; sigQual ::= "abstract" | "lone" | "one" | "some" | "private"
  (pSigQ ::= abstract lone one some)
  ;; sigExt ::= "extends" ref
  ;; sigExt ::= "in" ref ["+" ref]*
  (pSigX ::= (extends pRef))
  ;; expr ::=
  (pExpr ::= string)
  ;(let (ltd ...) pBlock)    ;; | "let" letDecl,+ blockOrBar
  ;(pQuant (dcl ...) pBlock) ;; | quant decl,+    blockOrBar
  ;(pUOP pExpr)              ;; | unOp expr
  ; (pBOP pExpr pExpr)        ;; | expr binOp   expr
  ; (pCOP pExpr pExpr)        ;; | expr ["!"|"not"] compareOp expr
  ; integer                   ;; | number
  ; none                      ;; | "none"
  ; iden                      ;; | "iden"
  ; univ                      ;; | "univ"
  ;; | expr ("=>"|"implies") expr "else" expr
  ;; | expr arrowOp expr
  ;; | expr "[" expr,* "]"
  ;; | "Int"
  ;; | "seq/Int"
  ;; | "(" expr ")"
  ;; | ["@"] name
  ;; | block
  ;; | "{" decl,+ blockOrBar "}"
  ;)
  ; block ::= "{" expr* "}"
  ; blockOrBar ::= block
  ; blockOrBar ::= "|" expr
  (pBlock ::= (pExpr ...))
  ;; decl ::= ["private"] ["disj"] name,+ ":" ["disj"] expr
  (pDecl ::= (pName pExpr))
  ;; letDecl ::= name "=" expr
  (pLet ::= (pName pExpr))
  ;; quant ::= "all" | "no" | "some" | "lone" | "one" | "sum"
  (pQuant ::= all no some lone one)
  ;; binOp ::= "||" | "or" | "&&" | "and" | "&" | "<=>" | "iff"
  ;;        | "=>" | "implies" | "+" | "-" | "++" | "<:" | ":>" | "." | "<<" | ">>" | ">>>"
  (pBOP ::= \| & => <=> + - \.)
  ;; arrowOp ::= ["some"|"one"|"lone"|"set"] "->" ["some"|"one"|"lone"|"set"]
  ;TODO
  ;; compareOp ::= "=" | "in" | "<" | ">" | "=<" | ">="
  (pCOP ::= = in < > =< >=)
  ; unOp ::= "!" | "no" | "some" | "lone" | "one" | "set" | "seq" | "#" | "~" | "*" | "^"
  (pUOP ::= ! no some lone one set \# ~ * ^)
  ; name ::= ("this" | ID) ["/" ID]*
  (pName ::= string)
  ; ref ::= name | "univ" | "Int" | "seq/Int"
  (pRef ::= pName univ)
  )
(render-language ALLOY)
#|||||||||
| Typing |
|||||||||#
;TODO
(define-judgment-form ALLOY
  #:mode (typeof I I O)
  #:contract (typeof a b c)
  ((typeof d e f))
  ((typeof g h i))
  ;...
  )
#||||||||||||
| Semantics |
||||||||||||#
(define R
  (reduction-relation
   ALLOY #:domain SPEC
   (--> pALLOY (rALLOY pALLOY))
   ))
(define-metafunction ALLOY
  rALLOY : any -> any
  ((rALLOY (pPar ...)) ((rPar pPar) ...)))
(define-metafunction ALLOY
  rPar : any -> any
  ((rPar pFact) "fact")
  ((rPar pFunc) "func")
  ((rPar pCmd) "cmd")
  ((rPar pSig) "sig"))
#|||||||||||
| Examples |
|||||||||||#
(define (trace spec) (traces R spec))
(define x1 (term (rALLOY
                  ((fact "foo" ("expr1"
                                "expr2"
                                "expr3"))
                   (fact "bar" ("exprA"))
                   (func "add1" (("x" "Int")
                                 ("y" "Int"))
                         "expr1"
                         ())
                   ))))
(define x2 (term (rALLOY
                  ((sig (abstract some) ("State") (extends univ)
                        ("expr1"
                         "expr2"
                         "expr3"))
                   (sig (one) ("StateA" "StateB" "StateC") (extends "State")
                        ())
                   ))))
(define x3 (term (rALLOY
                  ((cmd "verifyTypeSoundness"
                        ("block1"
                         "block2"
                         "block3")
                        (for 7 ()))
                   (cmd "show" () (for 7 ((exactly 2 "Cat")
                                          (4 "Dog"))))
                   ))))
