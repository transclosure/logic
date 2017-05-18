#lang racket
(require redex/reduction-semantics)
(require redex/pict)

;; taken from http://alloy.mit.edu/alloy/documentation/alloy4-grammar.txt
;; flagrant (essentially sugar) and pedantic (unhelpful disjunction) syntax are omitted
;; some useful but highly expressive syntax left out for now
(define-language Alloy
  ;; specification ::= [module] open* paragraph*
  (spc ::= (par ...))
  ;; module ::= "module" name  [ "["  ["exactly"] name  ("," ["exactly"] num)*    "]" ]
  ;TODO(mod ::= ("module" nm  ["[" ["exactly"] nm ("," ["exactly"] num)* "]"]))
  ;; open ::= ["private"]  "open"  name  [ "[" ref,+ "]" ]  [ "as" name ]
  ;TODO(opn ::= (["private"] "open" nm ["["ref"]"] ["as" nm]))
  ;; paragraph ::= factDecl | assertDecl | funDecl | cmdDecl | enumDecl | sigDecl
  (par ::= fact fun cmd sig)
  ;; factDecl ::= "fact" [name] block
  (fact ::= (fact nm blk))
  ;; assertDecl ::= "assert" [name] block
  ;TODO(asrt ::= ("assert" [nm] blk))
  ;; funDecl ::= ["private"] "fun" [ref "."] name "(" decl,* ")" ":" expr block
  ;; funDecl ::= ["private"] "fun" [ref "."] name "[" decl,* "]" ":" expr block
  ;; funDecl ::= ["private"] "fun" [ref "."] name                ":" expr block
  ;; funDecl ::= ["private"] "pred" [ref "."] name "(" decl,* ")" block
  ;; funDecl ::= ["private"] "pred" [ref "."] name "[" decl,* "]" block
  ;; funDecl ::= ["private"] "pred" [ref "."] name                block
  (fun ::= (fun nm (dcl ...) expr blk))
  ;; cmdDecl ::= [name ":"] ("run"|"check") (name|block) scope
  (cmd ::= (cmd nm blk scp))
  ;; scope ::= "for" number                   ["expect" (0|1)]
  ;; scope ::= "for" number "but" typescope,+ ["expect" (0|1)]
  ;; scope ::= "for"              typescope,+ ["expect" (0|1)]
  ;; scope ::=                                ["expect" (0|1)]
  (scp ::= [natural (tscp ...)])
  ;; typescope ::= ["exactly"] number [name|"int"|"seq"]
  (tscp ::= [exactly natural nm] [natural nm])
  ;; enumDecl ::= "enum" name "{" name  ("," name)*  "}"
  ;TODO
  ;; sigDecl ::= sigQual* "sig" name,+ [sigExt] "{" decl,* "}" [block]
  (sig ::= (sig (sigq ...) (nm ...) sigx (dcl ...)))
  ;; sigQual ::= "abstract" | "lone" | "one" | "some" | "private"
  (sigq ::= abstract lone one some)
  ;; sigExt ::= "extends" ref
  ;; sigExt ::= "in" ref ["+" ref]*
  (sigx ::= [extends rf])
  ;; expr ::= 
  (expr ::= (let (ltd ...) blk) ;; | "let" letDecl,+ blockOrBar
        (qnt (dcl ...) blk)     ;; | quant decl,+    blockOrBar
        (uop expr)              ;; | unOp expr
        (bop expr expr) ;; | expr binOp   expr
        ;;       | expr ("=>"|"implies") expr "else" expr
        ;;       | expr arrowOp expr
        (cop expr expr) ;;       | expr ["!"|"not"] compareOp expr
        ;;       | expr "[" expr,* "]"
        natural  ;;       |     number
        none ;;       | "none"
        iden ;;       | "iden"
        univ ;;       | "univ"
        ;;       | "Int"
        ;;       | "seq/Int"
        (expr) ;;       | "(" expr ")"
        ;;       | ["@"] name
        blk  ;;       | block
        ;;       | "{" decl,+ blockOrBar "}"
        )
  ;; decl ::= ["private"] ["disj"] name,+ ":" ["disj"] expr
  (dcl ::= [(nm ...) expr])
  ;; letDecl ::= name "=" expr
  (ltd ::= [nm expr])
  ;; quant ::= "all" | "no" | "some" | "lone" | "one" | "sum"
  (qnt ::= all no some lone one)
  ;; binOp ::= "||" | "or" | "&&" | "and" | "&" | "<=>" | "iff"
  ;;        | "=>" | "implies" | "+" | "-" | "++" | "<:" | ":>" | "." | "<<" | ">>" | ">>>"
  (bop ::= \| & => <=> + - \.)
  ;; arrowOp ::= ["some"|"one"|"lone"|"set"] "->" ["some"|"one"|"lone"|"set"]
  ;TODO
  ;; compareOp ::= "=" | "in" | "<" | ">" | "=<" | ">="
  (cop ::= = in < > =< >=)
  ; unOp ::= "!" | "no" | "some" | "lone" | "one" | "set" | "seq" | "#" | "~" | "*" | "^"
  (uop ::= ! no some lone one set \# ~ * ^)
  ; block ::= "{" expr* "}"
  ; blockOrBar ::= block
  ; blockOrBar ::= "|" expr
  (blk ::= (expr ...))
  ; name ::= ("this" | ID) ["/" ID]*
  (nm ::= string)
  ; ref ::= name | "univ" | "Int" | "seq/Int"
  (rf ::= nm univ)
  )
(render-language Alloy)


