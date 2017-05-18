#lang rosette
;; mandatory
(require ocelot)
(require redex/reduction-semantics)
;; optional
(require redex/pict)
(require redex/gui)

;; taken from http://alloy.mit.edu/alloy/documentation/alloy4-grammar.txt
;; flagrant (essentially sugar) and pedantic (unhelpful disjunction) syntax are omitted
;; some useful but highly expressive syntax left out for now
(define-language Alloy
  (pSPEC ::= pALLOY pOCELOT)
  (pOCELOT ::= string) ;TODO how to hook in ocelot syntax tree???
  ;; specification ::= [module] open* paragraph*
  (pALLOY ::= (pPar ...+))
  ;; module ::= "module" name  [ "["  ["exactly"] name  ("," ["exactly"] num)*    "]" ]
  ;TODO(mod ::= ("module" nm  ["[" ["exactly"] nm ("," ["exactly"] num)* "]"]))
  ;; open ::= ["private"]  "open"  name  [ "[" ref,+ "]" ]  [ "as" name ]
  ;TODO(opn ::= (["private"] "open" nm ["["ref"]"] ["as" nm]))
  ;; paragraph ::= factDecl | assertDecl | funDecl | cmdDecl | enumDecl | sigDecl
  (pPar ::= pFact pFunc pCmd pSig)
  ;; factDecl ::= "fact" [name] block
  (pFact ::= (fact pName)); blk))
  ;; assertDecl ::= "assert" [name] block
  ;TODO(asrt ::= ("assert" [nm] blk))
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
  (pSig ::= (sig (pSigQ ...) (pName ...+) pSigX (pDecl ...)))
  ;; sigQual ::= "abstract" | "lone" | "one" | "some" | "private"
  (pSigQ ::= abstract lone one some)
  ;; sigExt ::= "extends" ref
  ;; sigExt ::= "in" ref ["+" ref]*
  (pSigX ::= (extends pRef))
  ;; expr ::= 
  (pExpr ::=
         (let (ltd ...) pBlock)    ;; | "let" letDecl,+ blockOrBar
         (pQuant (dcl ...) pBlock) ;; | quant decl,+    blockOrBar
         (pUOP pExpr)              ;; | unOp expr
         (pBOP pExpr pExpr)        ;; | expr binOp   expr
         (pCOP pExpr pExpr)        ;; | expr ["!"|"not"] compareOp expr
         integer                   ;; | number
         none                      ;; | "none"
         iden                      ;; | "iden"
         univ                      ;; | "univ"
         ;; | expr ("=>"|"implies") expr "else" expr
         ;; | expr arrowOp expr
         ;; | expr "[" expr,* "]"
         ;; | "Int"
         ;; | "seq/Int"
         ;; | "(" expr ")"
         ;; | ["@"] name
         ;; | block
         ;; | "{" decl,+ blockOrBar "}"
         )
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
(render-language Alloy)
;TODO well-typed Alloy (define-judgements)

;; Reductions (Surfae ALLOY --R-> Core ALLOY --F-> OCELOT)
(define R
  (reduction-relation
   Alloy #:domain SPEC
   (--> (pPar) (fPar pPar) isthisarbitrary)
   ;   (--> (O V ...) (δ O V ...) δ) primitive case!!! (apply 2nd metafunc)
   ;   (--> (if0 0 M_0 M_1) M_0 if0-t) trivial case!!! (no need to do prim op)
   ))

;; (meta)Functions (Core ALLOY --F-> OCELOT)
(define-metafunction Alloy
  [(rPar pFact) "fact"]
  [(rPar pFunc) "func"]
  [(rPar pCmd) "cmd"]
  [(rPar pSig) "sig"])

(traces R (term
           ((rPar (fact "foo"))
            (rPar (fact "bar"))
            )
           ))
