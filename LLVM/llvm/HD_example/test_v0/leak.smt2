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
(rule (KEY_SENSITIVE #b00000011))
;### Begin facts 
;   %0 = load i32* %i1.addr, align 4
(rule (assign #b00001100 #b00000001))
;   %1 = load i32* %i2.addr, align 4
(rule (assign #b00001101 #b00000010))
;   %xor = xor i32 %0, %1
(rule (assign #b00001110 #b00001100))
;   %xor = xor i32 %0, %1
(rule (assign #b00001110 #b00001101))
;   store i32 %xor, i32* %n1, align 4
(rule (assign #b00000101 #b00001110))
;   %2 = load i32* %n1, align 4
(rule (assign #b00010000 #b00000101))
;   %3 = load i32* %key.addr, align 4
(rule (assign #b00010001 #b00000011))
;   %xor1 = xor i32 %2, %3
(rule (assign #b00010010 #b00010000))
;   %xor1 = xor i32 %2, %3
(rule (assign #b00010010 #b00010001))
;   store i32 %xor1, i32* %n2, align 4
(rule (assign #b00000110 #b00010010))
;   %4 = load i32* %n2, align 4
(rule (assign #b00010100 #b00000110))
;   %5 = load i32* %i3.addr, align 4
(rule (assign #b00010101 #b00000100))
;   %and = and i32 %4, %5
(rule (assign #b00010110 #b00010100))
;   %and = and i32 %4, %5
(rule (assign #b00010110 #b00010101))
;   store i32 %and, i32* %n3, align 4
(rule (assign #b00000111 #b00010110))
;   %6 = load i32* %n3, align 4
(rule (assign #b00011000 #b00000111))
;###### End Facts

(query KEY_SENSITIVE :print-answer true)
