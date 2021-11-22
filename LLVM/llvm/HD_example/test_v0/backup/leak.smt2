(set-option :fixedpoint.engine datalog)
; this sort is used to define all the relations
(define-sort s () (_ BitVec 32))

; assignment (assign from to)
(declare-rel assign(s, s))
; DEP relation: (DEP xxx, xxx)
(declare-rel DEP (s, s))

(declare-var var s)
(declare-var prev s)
(declare-var to s)
(declare-var from s)

; the DEP relation defines what it depends on
(rule (=> (assign to from) (DEP to from)))

; transitive closure of its assignments(rule (=> (and (assign to from) (DEP from prev)) (DEP to prev)))

;###### End Facts
