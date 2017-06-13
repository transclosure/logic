#lang rosette
#|||||||||||||||||||||||||||||||||||||||
| Alloy Compiler for Ocelot/Rosette/Z3 |
|||||||||||||||||||||||||||||||||||||||#
(require ocelot
         redex/reduction-semantics
         redex/pict
         redex/gui)
(provide )
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
  (pFunc ::= (func pName pExpr (pDecl ...) pExpr))
  ;; cmdDecl ::= [name ":"] ("run"|"check") (name|block) scope
  (pCmd ::= (cmd pName pExpr pScope))
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
  (pBop ::= \| & => <=> + - \.)
  ;; arrowOp ::= ["some"|"one"|"lone"|"set"] "->" ["some"|"one"|"lone"|"set"]
  ;TODO
  ;; compareOp ::= "=" | "in" | "<" | ">" | "=<" | ">="
  (pCop ::= = in < > =< >=)
  ; unOp ::= "!" | "no" | "some" | "lone" | "one" | "set" | "seq" | "#" | "~" | "*" | "^"
  (pUop ::= ! no some lone one set \# ~ * ^)
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
  ((rPar pFact) (rFact pFact))
  ((rPar pFunc) (rFunc pFunc))
  ((rPar pCmd)  (rCmd pCmd))
  ((rPar pSig)  (rSig pSig)))
(define-metafunction ALLOY
  rFact : any -> any
  ((rFact (fact pName pBlock)) (define pName (rBlock pBlock))))
;rfunc
(define-metafunction ALLOY
  rCmd : any -> any
  ((rCmd (cmd pName pExpr pScope)) "TODO"))
;rscope
;rsig
(define-metafunction ALLOY
  rExpr : any -> any
  ((rExpr pExpr) pExpr))
(define-metafunction ALLOY
  rBlock : any -> any
  ((rBlock ()) #t)
  ((rBlock (pExpr ...)) (and (rExpr pExpr) ...)))
;rdecl
;rlet
#|||||||||||
| Examples |
|||||||||||#
(define (trace spec) (traces R spec))
(define (xfact) (term (rALLOY
                       ((fact "factname1" ("conjunctexpr1"
                                           "conjunctexpr2"
                                           "conjunctexpr3"))
                        (fact "factname2" ())
                        ))))
(define (xfunc) (term (rALLOY
                       ((func "funcname" "outputtypeexpr" (("inputvar1" "typeexpr")
                                                           ("inputvar2" "typeexpr"))
                              "funcexpr")
                        ))))
(define (xsig) (term (rALLOY
                      ((sig (abstract some) ("State") (extends univ)
                            ("relationexpr1"
                             "relationexpr2"
                             "relationexpr3"))
                       (sig (one) ("StateA" "StateB" "StateC") (extends "State") ())
                       ))))
(define (xcmd) (term (rALLOY
                      ((cmd "cmdname"
                            "cmdexpr"
                            (for 7 ()))
                       (cmd "show"
                            "cmdexpr"
                            (for 7 ((exactly 2 "Cat")
                                    (4 "Dog"))))
                       ))))
