(set-option :fixedpoint.engine datalog)
; this sort is used to define all the relations
(define-sort s () (_ BitVec 8))
(define-sort Set () (Array s bool))

; assignment (assign from to)
(declare-rel assign(s s))
; xor_assignment (xor_assign from to)
(declare-rel xor_assign(s s))
; TDEP relation: (TDEP xxx, xxx)
(declare-rel TDEP (s s))
; KEY_SENSITIVE relation: KEY_SENSITIVE(var)
(declare-rel KEY_INCLUDE (s Set))
(declare-rel PLAIN_INCLUDE (s Set))
(declare-rel RAND_INCLUDE (s Set))
; define the variables which involved with the xor operation (^ var)
(declare-rel XOR_INCLUDE (s Set))
; all the variables existence ====> (r1 r2.... k1 k2... p1 p2...)
(declare-rel ALL_INCLUDE (s Set))

(declare-rel KEY_SENSITIVE (s))
(declare-rel KEY_IND (s))
(declare-rel PLAIN (s))
; Random variable dependence array [only used for the "random" type; for other types, the RAND_VAR set is empty]
(declare-rel RAND_VAR (s Set))
; Is Empty Relation
(declare-rel IS_EMPTY (s))

(declare-var var s)
(declare-var prev s)
(declare-var to s)
(declare-var from s)
(declare-var from1 s)
(declare-var from2 s)
(declare-var RAND_A Set)
(declare-var RAND_B Set)
(declare-var RAND_C Set)
(declare-var RAND_INC_A Set)
(declare-var RAND_INC_B Set)
(declare-var RAND_INC_C Set)
(declare-var XOR_INC_A Set)
(declare-var XOR_INC_B Set)
(declare-var XOR_INC_C Set)
(declare-var ALL_INC_A Set)
(declare-var ALL_INC_B Set)
(declare-var ALL_INC_C Set)
(declare-var NONE_Set Set)
(assert (= NONE_Set ((as const (Array s bool)) false)))

; set theory operation define
; "Intersection" Operation
(define-fun set_intersect ((x Set) (y Set)) Set ((_ map and) x y))
(define-fun IsEmpty ((x Set)) bool
(forall ((ind s) (x_in Set)) (and (= x_in x) (not (select x_in ind))))
)
;; for testing if function "IsEmpty" can be used in the rules and assertion
;(assert (=> (and (IsEmpty RAND_A) (RAND_VAR var RAND_A)) (IS_EMPTY var)))

; "Diff" Op : xor x ^ y = (~x & y) | (x & ~y)
; "Diff" x\y = x & (x ^ y)
(define-fun set_diff ((x Set) (y Set)) Set
((_ map and) x ((_ map or) ((_ map and) ((_ map not) x) y) ((_ map and) x ((_ map not) y))))
)

; "Set-Or" operation
(define-fun set_or ((x Set) (y Set)) Set
((_ map or) x y)
)

; "Set-Sum" op: (x,y) = (x + y) - (x ^ y)
(define-fun set_sum ((x Set) (y Set)) Set
((_ map or) ((_ map and) ((_ map not) x) y) ((_ map and) x ((_ map not) y)))
)

; "Ret-Type" return the type of the given variable TO DO!!
;(define-fun Ret-Type ())

; the TDEP relation defines what it transitively depends on
(rule (=> (assign to from) (TDEP to from)))
; transitive closure of its assignments
(rule (=> (and (assign to from) (TDEP from prev)) (TDEP to prev)))
; the relation between assign and xor_assign
(rule (=> (xor_assign to from) (assign to from)))
(rule (=> (and (xor_assign to from) (assign from prev)) (assign to prev)))
; transitive closure of its assignments
(rule (=> (and (assign to from) (KEY_SENSITIVE from)) (KEY_SENSITIVE to)))

; xor operation
(rule (=> (and (xor_assign to from1) (xor_assign to from2) (not (IsEmpty RAND_A)) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (RAND_VAR to RAND_C) (IsEmpty (set_intersect RAND_A RAND_B))) (= RAND_C (set_sum RAND_A RAND_B))))

(rule (=> (and (xor_assign to from1) (xor_assign to from2) (not (IsEmpty RAND_B)) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (RAND_VAR to RAND_C) (IsEmpty (set_intersect RAND_A RAND_B))) (= RAND_C (set_sum RAND_A RAND_B))))

; xor operation RAND + RAND  ====>  (A\B != empty) Or (B\A != empty)  
(rule (=> (and (xor_assign to from1) (xor_assign to from2) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (RAND_VAR to RAND_C) (not (IsEmpty RAND_A)) (not (IsEmpty RAND_B)) (or (not (IsEmpty (set_diff RAND_A RAND_B))) (not (IsEmpty (set_diff RAND_B RAND_A))))) (= RAND_C (set_sum RAND_A RAND_B))))

; xor operation RAND + RAND ====>(1) (A\B == empty) And (B\A == empty) And (SID) => SID
; (2) (A\B == empty) And (B\A ==empty) And (~SID) And (key_include) => Key_sensitive
(rule (=> (and (xor_assign to from1) (xor_assign to from2) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (RAND_VAR to RAND_C) (not (IsEmpty RAND_A)) (not (IsEmpty RAND_B)) (and (IsEmpty (set_diff RAND_A RAND_B)) (IsEmpty (set_diff RAND_B RAND_A))) (and (KEY_IND from1) (KEY_IND from2))) (and (= RAND_C (set_diff RAND_A RAND_B)) (KEY_IND to))))

(rule (=> (and (xor_assign to from1) (xor_assign to from2) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (RAND_VAR to RAND_C) (not (IsEmpty RAND_A)) (not (IsEmpty RAND_B)) (and (IsEmpty (set_diff RAND_A RAND_B)) (IsEmpty (set_diff RAND_B RAND_A))) (or (not (KEY_IND from1)) (not (KEY_IND from2)))) (and (= RAND_C (set_diff RAND_A RAND_B)) (KEY_SENSITIVE to))))

; xor operation RAND + SID + (RAND(r1,r2..)\(RAND_INC(r1,r2..) in SID) != empty) ====> RAND
(rule (=> (and (xor_assign to from1) (xor_assign to from2) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (RAND_VAR to RAND_C) (RAND_INCLUDE from1 RAND_INC_A) (RAND_INCLUDE from2 RAND_INC_B) (RAND_INCLUDE to RAND_INC_C) (or (and (KEY_IND from1) (IsEmpty RAND_A) (not (IsEmpty RAND_B)) (not (IsEmpty (set_diff RAND_B RAND_INC_A)))) (and (KEY_IND from2) (IsEmpty RAND_B) (not (IsEmpty RAND_A)) (not (IsEmpty (set_diff RAND_A RAND_INC_B)))))) (and (= RAND_C (set_or RAND_A RAND_B)) (KEY_IND to) (= RAND_INC_C (set_or RAND_INC_A RAND_INC_B)))))

; xor operation RAND + SID + else(RAND \ (RAND_INC in SID) == empty ) ========> KEY_SENSITIVE
(rule (=> (and (xor_assign from1 to) (xor_assign from2 to) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (RAND_VAR to RAND_C) (RAND_INCLUDE from1 RAND_INC_A) (RAND_INCLUDE from2 RAND_INC_B) (RAND_INCLUDE to RAND_INC_C) (or (and (KEY_IND from2) (IsEmpty RAND_B) (not (IsEmpty RAND_A)) (IsEmpty (set_diff RAND_A RAND_INC_B))) (and (KEY_IND from1) (IsEmpty RAND_A) (not (IsEmpty RAND_B)) (IsEmpty (set_diff RAND_B RAND_INC_A))))) (and (KEY_SENSITIVE to) (= RAND_C NONE_Set) (= RAND_INC_C (set_or RAND_INC_A RAND_INC_B)))))

;xor operation SID + SID + (intersect (ALL_INC_A, ALL_INC_B) == empty) ===> SID (most precise condition)
(rule (=> (and (xor_assign to from1) (xor_assign to from2) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (ALL_INCLUDE to ALL_INC_C) (RAND_INCLUDE from1 RAND_INC_A) (RAND_INCLUDE from2 RAND_INC_B) (RAND_INCLUDE to RAND_INC_C) (KEY_IND from1) (KEY_IND from2) (IsEmpty (set_intersect ALL_INC_A ALL_INC_B))) (and (KEY_IND to) (= ALL_INC_C (set_or ALL_INC_A ALL_INC_B)) (= RAND_INC_C (set_or RAND_INC_A RAND_INC_B)))))

; xor operation SID + SID + ((XOR_INC(r1 r2 r3...) \ (XOR_INC (r1 e2..) in SID)) != empty)  ======> SID
(rule (=> (and (xor_assign to from1) (xor_assign to from2) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (RAND_VAR to RAND_C) (KEY_IND from1) (KEY_IND from2) (IsEmpty RAND_A) (IsEmpty RAND_B) (or (not (IsEmpty (set_diff XOR_INC_A XOR_INC_B))) (not (IsEmpty (set_diff XOR_INC_B XOR_INC_A)))) (XOR_INCLUDE from1 XOR_INC_A) (XOR_INCLUDE from2 XOR_INC_B) (XOR_INCLUDE to XOR_INC_C)) (and (KEY_IND to) (= XOR_INC_C (set_or XOR_INC_A XOR_INC_B)) (= RAND_C (set_or RAND_A RAND_B)))))

; xor operation SID + SID + (XOR_INC_A == XOR_INC_B)
; xor operation RAND + KEY_SENSITIVE ==> TO DO

; other operations
(rule (=> (and (assign to from1) (assign to from2) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (RAND_VAR to RAND_C) (not (IsEmpty RAND_A)) (IsEmpty (set_intersect RAND_A RAND_B))) (KEY_IND to)))

(rule (=> (and (assign to from1) (assign to from2) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (RAND_VAR to RAND_C) (not (IsEmpty RAND_B)) (IsEmpty (set_intersect RAND_A RAND_B))) (KEY_IND to)))


; user specify the sensitive variable
(rule (KEY_SENSITIVE #b00010001))
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
