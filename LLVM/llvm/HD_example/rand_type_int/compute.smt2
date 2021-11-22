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
;   %0 = load i32* %k.addr, align 4
(rule (assign #b00001111 #b00000100))
;   %1 = load i32* %r2.addr, align 4
(rule (assign #b00010000 #b00000010))
;   %xor = xor i32 %0, %1
(rule (xor_assign #b00010001 #b00001111))
;   %xor = xor i32 %0, %1
(rule (xor_assign #b00010001 #b00010000))
;   store i32 %xor, i32* %c1, align 4
(rule (assign #b00000101 #b00010001))
;   %2 = load i32* %r1.addr, align 4
(rule (assign #b00010011 #b00000001))
;   %3 = load i32* %r2.addr, align 4
(rule (assign #b00010100 #b00000010))
;   %xor1 = xor i32 %2, %3
(rule (xor_assign #b00010101 #b00010011))
;   %xor1 = xor i32 %2, %3
(rule (xor_assign #b00010101 #b00010100))
;   store i32 %xor1, i32* %c2, align 4
(rule (assign #b00000110 #b00010101))
;   %4 = load i32* %c2, align 4
(rule (assign #b00010111 #b00000110))
;   %5 = load i32* %c1, align 4
(rule (assign #b00011000 #b00000101))
;   %xor2 = xor i32 %4, %5
(rule (xor_assign #b00011001 #b00010111))
;   %xor2 = xor i32 %4, %5
(rule (xor_assign #b00011001 #b00011000))
;   store i32 %xor2, i32* %c3, align 4
(rule (assign #b00000111 #b00011001))
;   %6 = load i32* %c3, align 4
(rule (assign #b00011011 #b00000111))
;   %7 = load i32* %c2, align 4
(rule (assign #b00011100 #b00000110))
;   %xor3 = xor i32 %6, %7
(rule (xor_assign #b00011101 #b00011011))
;   %xor3 = xor i32 %6, %7
(rule (xor_assign #b00011101 #b00011100))
;   store i32 %xor3, i32* %c4, align 4
(rule (assign #b00001000 #b00011101))
;   %8 = load i32* %c4, align 4
(rule (assign #b00011111 #b00001000))
;   %9 = load i32* %r1.addr, align 4
(rule (assign #b00100000 #b00000001))
;   %xor4 = xor i32 %8, %9
(rule (xor_assign #b00100001 #b00011111))
;   %xor4 = xor i32 %8, %9
(rule (xor_assign #b00100001 #b00100000))
;   store i32 %xor4, i32* %c5, align 4
(rule (assign #b00001001 #b00100001))
;   %10 = load i32* %c5, align 4
(rule (assign #b00100011 #b00001001))
;   %11 = load i32* %r3.addr, align 4
(rule (assign #b00100100 #b00000011))
;   %and = and i32 %10, %11
(rule (assign #b00100101 #b00100011))
;   %and = and i32 %10, %11
(rule (assign #b00100101 #b00100100))
;   store i32 %and, i32* %c6, align 4
(rule (assign #b00001010 #b00100101))
;   %12 = load i32* %c6, align 4
(rule (assign #b00100111 #b00001010))
;###### End Facts
