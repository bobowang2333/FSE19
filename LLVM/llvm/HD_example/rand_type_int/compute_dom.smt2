(set-option :fixedpoint.engine datalog)
(define-sort s () (_ BitVec 8))
(define-sort BitSet () (_ BitVec 4))

; assignment (assign to from)
(declare-rel assign(s s))
(declare-rel xor_assign_left (s s))
(declare-rel xor_assign_right (s s))
(declare-rel andor_assign_left (s s))
(declare-rel andor_assign_right (s s))
(declare-rel not_assign (s))
(declare-rel load_assign (s s))
(declare-rel store_assign (s s))

; define the relations for RAND_VAR(dom) and ALL_INC(semd)
(declare-rel dom (s BitSet))
(declare-rel dom_common (s BitSet))
(declare-rel semd (s BitSet))
(declare-rel semd_not (s BitSet))
(declare-rel RAND (s))
;;;; if <s> has types such as RAND, KEY_IND or KEY_SENSITIVE, then 
(declare-rel type (s BitSet))

; define the variables which may be used in the rule
(declare-var from1 s)
(declare-var from2 s)
(declare-var to s)
(declare-var X BitSet)
(declare-var Y BitSet)


;;;; rules definition;;;;;;;;
;; [XOR-RUD1]
;; the update of the set <semd> and <dom> has some problems in this way
(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (dom from1 X) (semd_not from2 X) (RAND from1)) (RAND to)))
(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (dom from1 X) (semd_not from2 X) (RAND from1)) (dom to X)))
(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (dom from1 X) (dom from2 X) (RAND from1)) (dom_common to X)))
(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (RAND from1) ) (dom to X)))


;; undecided types => key_sensitive types

;; define the dom and semd for the input variables;;;;
;### Begin facts
;   %0 = load i32* %k.addr, align 4
(rule (load_assign #b00001111 #b00000100))
;   %1 = load i32* %r2.addr, align 4
(rule (load_assign #b00010000 #b00000010))
;   %xor = xor i32 %0, %1
(rule (xor_assign_left #b00010001 #b00001111))
;   %xor = xor i32 %0, %1
(rule (xor_assign_right #b00010001 #b00010000))
;   store i32 %xor, i32* %c1, align 4
(rule (store_assign #b00000101 #b00010001))
;   %2 = load i32* %r1.addr, align 4
(rule (load_assign #b00010011 #b00000001))
;   %3 = load i32* %r2.addr, align 4
(rule (load_assign #b00010100 #b00000010))
;   %xor1 = xor i32 %2, %3
(rule (xor_assign_left #b00010101 #b00010011))
;   %xor1 = xor i32 %2, %3
(rule (xor_assign_right #b00010101 #b00010100))
;   store i32 %xor1, i32* %c2, align 4
(rule (store_assign #b00000110 #b00010101))
;   %4 = load i32* %c2, align 4
(rule (load_assign #b00010111 #b00000110))
;   %5 = load i32* %c1, align 4
(rule (load_assign #b00011000 #b00000101))
;   %xor2 = xor i32 %4, %5
(rule (xor_assign_left #b00011001 #b00010111))
;   %xor2 = xor i32 %4, %5
(rule (xor_assign_right #b00011001 #b00011000))
;   store i32 %xor2, i32* %c3, align 4
(rule (store_assign #b00000111 #b00011001))
;   %6 = load i32* %c3, align 4
(rule (load_assign #b00011011 #b00000111))
;   %7 = load i32* %c2, align 4
(rule (load_assign #b00011100 #b00000110))
;   %xor3 = xor i32 %6, %7
(rule (xor_assign_left #b00011101 #b00011011))
;   %xor3 = xor i32 %6, %7
(rule (xor_assign_right #b00011101 #b00011100))
;   store i32 %xor3, i32* %c4, align 4
(rule (store_assign #b00001000 #b00011101))
;   %8 = load i32* %c4, align 4
(rule (load_assign #b00011111 #b00001000))
;   %9 = load i32* %r1.addr, align 4
(rule (load_assign #b00100000 #b00000001))
;   %xor4 = xor i32 %8, %9
(rule (xor_assign_left #b00100001 #b00011111))
;   %xor4 = xor i32 %8, %9
(rule (xor_assign_right #b00100001 #b00100000))
;   store i32 %xor4, i32* %c5, align 4
(rule (store_assign #b00001001 #b00100001))
;   %10 = load i32* %c5, align 4
(rule (load_assign #b00100011 #b00001001))
;   %11 = load i32* %r3.addr, align 4
(rule (load_assign #b00100100 #b00000011))
;   %and = and i32 %10, %11
(rule (andor_assign_left #b00100101 #b00100011))
;   %and = and i32 %10, %11
(rule (andor_assign_right #b00100101 #b00100100))
;   store i32 %and, i32* %c6, align 4
(rule (store_assign #b00001010 #b00100101))
;   %12 = load i32* %c6, align 4
(rule (load_assign #b00100111 #b00001010))
;###### End Facts
(query RAND :print-answer true)
