(set-option :fixedpoint.engine datalog)
; this sort is used to define all the relations
(define-sort s () (_ BitVec 8))
(define-sort Set () (Array s bool))

; assignment (assign from to)
(declare-rel assign(s s))
(declare-rel xor_assign(s s))
; TDEP relation: (TDEP xxx, xxx)
(declare-rel TDEP (s s))
; KEY_SENSITIVE relation: KEY_SENSITIVE(var)
(declare-rel KEY_SENSITIVE (s))
(declare-rel KEY_IND (s))
(declare-rel PLAIN (s))
(declare-rel RAND (s))

; For [RAND] type, TRUE denote that the variable depends on which random value
(declare-rel RAND_VAR (s Set))
; all the variables existence ======> (r1 r2 ... k1 k2 ... p1 p2 ...)
(declare-rel ALl_INCLUDE (s Set))

(declare-var var s)
(declare-var prev s)
(declare-var to s)
(declare-var from s)

; the TDEP relation defines what it transitively depends on
(rule (=> (assign to from) (TDEP to from)))
(rule (=> (xor_assign to from) (assign to from)))

; transitive closure of its assignments
(rule (=> (and (assign to from) (TDEP from prev)) (TDEP to prev)))
; transitive closure of its assignments
(rule (=> (and (assign to from) (KEY_SENSITIVE from)) (KEY_SENSITIVE to)))

; user specify the sensitive variable (based on the input)
(rule (KEY_SENSITIVE #b00010001))
(rule (RAND #b00000001))
(rule (RAND #b00000010))
(rule (RAND #b00000011))

; build the random dependence relation
(declare-var RAND_r1 Set)
(declare-var RAND_r2 Set)
(declare-var RAND_r3 Set)
(assert (= (select RAND_r1 #b00000000) true))
(assert (= (select RAND_r2 #b00000001) true))
(assert (= (select RAND_r3 #b00000010) true))
(rule (RAND_VAR #b00000001 RAND_r1))
(rule (RAND_VAR #b00000010 RAND_r2))
(rule (RAND_VAR #b00000011 RAND_r3))

;### Begin facts 
;   store i8 %frombool, i8* %r1.addr, align 1
(rule (assign #b00000001 #b00001011))
;   store i8 %frombool1, i8* %r2.addr, align 1
(rule (assign #b00000010 #b00001101))
;   store i8 %frombool2, i8* %r3.addr, align 1
(rule (assign #b00000011 #b00001111))
;   store i8 %frombool3, i8* %k.addr, align 1
(rule (assign #b00000100 #b00010001))
;   %0 = load i8* %k.addr, align 1
(rule (assign #b00010011 #b00000100))
;   %1 = load i8* %r2.addr, align 1
(rule (assign #b00010110 #b00000010))
;   %xor = xor i32 %conv, %conv5
(rule (xor_assign #b00011001 #b00010101))
;   %xor = xor i32 %conv, %conv5
(rule (xor_assign #b00011001 #b00011000))
;   store i8 %frombool7, i8* %c1, align 1
(rule (assign #b00000101 #b00011011))
;   %2 = load i8* %r1.addr, align 1
(rule (assign #b00011101 #b00000001))
;   %3 = load i8* %r2.addr, align 1
(rule (assign #b00100000 #b00000010))
;   %xor12 = xor i32 %conv9, %conv11
(rule (xor_assign #b00100011 #b00011111))
;   %xor12 = xor i32 %conv9, %conv11
(rule (xor_assign #b00100011 #b00100010))
;   store i8 %frombool14, i8* %c2, align 1
(rule (assign #b00000110 #b00100101))
;   %4 = load i8* %c2, align 1
(rule (assign #b00100111 #b00000110))
;   %5 = load i8* %c1, align 1
(rule (assign #b00101010 #b00000101))
;   %xor19 = xor i32 %conv16, %conv18
(rule (xor_assign #b00101101 #b00101001))
;   %xor19 = xor i32 %conv16, %conv18
(rule (xor_assign #b00101101 #b00101100))
;   store i8 %frombool21, i8* %c3, align 1
(rule (assign #b00000111 #b00101111))
;   %6 = load i8* %c3, align 1
(rule (assign #b00110001 #b00000111))
;   %7 = load i8* %c2, align 1
(rule (assign #b00110100 #b00000110))
;   %xor26 = xor i32 %conv23, %conv25
(rule (xor_assign #b00110111 #b00110011))
;   %xor26 = xor i32 %conv23, %conv25
(rule (xor_assign #b00110111 #b00110110))
;   store i8 %frombool28, i8* %c4, align 1
(rule (assign #b00001000 #b00111001))
;   %8 = load i8* %c4, align 1
(rule (assign #b00111011 #b00001000))
;   %9 = load i8* %r1.addr, align 1
(rule (assign #b00111110 #b00000001))
;   %xor33 = xor i32 %conv30, %conv32
(rule (xor_assign #b01000001 #b00111101))
;   %xor33 = xor i32 %conv30, %conv32
(rule (xor_assign #b01000001 #b01000000))
;   store i8 %frombool35, i8* %c5, align 1
(rule (assign #b00001001 #b01000011))
;   %10 = load i8* %c5, align 1
(rule (assign #b01000101 #b00001001))
;   %11 = load i8* %r3.addr, align 1
(rule (assign #b01001000 #b00000011))
;   %and = and i32 %conv37, %conv39
(rule (assign #b01001011 #b01000111))
;   %and = and i32 %conv37, %conv39
(rule (assign #b01001011 #b01001010))
;   store i8 %frombool41, i8* %c6, align 1
(rule (assign #b00001010 #b01001101))
;   %12 = load i8* %c6, align 1
(rule (assign #b01001111 #b00001010))
;###### End Facts
