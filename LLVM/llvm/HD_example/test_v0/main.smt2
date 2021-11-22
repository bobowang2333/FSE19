(set-option :fixedpoint.engine datalog)
; this sort is used to define all the relations
(define-sort s () (_ BitVec 8))

; assignment (assign from to)
(declare-rel assign(s s))
; TDEP relation: (TDEP xxx, xxx)
(declare-rel TDEP (s s))
; KEY_SENSITIVE relation: KEY_SENSITIVE(var)
(declare-rel KEY_SENSITIVE (s))

(declare-var var s)
(declare-var prev s)
(declare-var to s)
(declare-var from s)

; the TDEP relation defines what it transitively depends on
(rule (=> (assign to from) (TDEP to from)))

; transitive closure of its assignments
(rule (=> (and (assign to from) (TDEP from prev)) (TDEP to prev)))
; transitive closure of its assignments
(rule (=> (and (assign to from) (KEY_SENSITIVE from)) (KEY_SENSITIVE to)))

; user specify the sensitive variable
(rule (KEY_SENSITIVE #b00010001))
;### Begin facts 
;   %0 = load i32* %i1, align 4
(rule (assign #b00100101 #b00011011))
;   %1 = load i32* %i2, align 4
(rule (assign #b00100110 #b00011100))
;   %2 = load i32* %i3, align 4
(rule (assign #b00100111 #b00011101))
;   %3 = load i32* %i4, align 4
(rule (assign #b00101000 #b00011110))
;   store i32 %call, i32* %res, align 4
(rule (assign #b00011111 #b00101001))
;   %4 = load i32* %res, align 4
(rule (assign #b00101011 #b00011111))
;###### End Facts
