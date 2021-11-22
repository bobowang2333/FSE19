(set-option :fixedpoint.engine datalog)
; this sort is used to define all the relations
(define-sort s () (_ BitVec 8))

; defining the set type for generating the random type, text type and key type 
(define-sort Set (T) (Array T bool))
(define-sort Res () (Array s bool))
; type: random ; while first Int is for random ID and the second Int is for variable %k
(declare-var RAND (Set s))
(assert (= RAND ((as const (Array s bool)) false)))

; option1: try to initial the value of this set for the random set ("s" type replace the "Int" above)
;(define-fun RAND () (Array Int Int bool) (_ as_array k!0))
;(define-fun k!0 ((x!0 Int) (x!1 Int)) bool (ite (and (= x!0 0) (= x!1 0)) 4 (ite (and (= x!0 0) (= x!1 1)) 5 6)))
; option2: initialize the value of this set for the random set
;(assert (= (select RAND 0 0) true))

; type: plain text && it will be in the form "PLAIN_V1"
;(declare-var PLAIN bool)
; type: secret information
;(declare-var SECRET bool)
; type: indepedent with key variable
;(declare-var IND bool)

; assignment (assign from to)
(declare-rel assign(s s))
; TDEP relation: (TDEP xxx, xxx)
(declare-rel TDEP (s s))
; KEY_SENSITIVE relation: KEY_SENSITIVE(var)
(declare-rel KEY_SENSITIVE (s))
; KEY_INDEPENDENT 
(declare-rel KEY_IND (s))
; Public Variable
(declare-rel PUB (s))

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

; user specify the random type
; [TEST] for var #b0000_0001
(assert (= (select RAND #b00000001) true))
(assert (= (select RAND #b00000011) true))
; for var #b000_1000
(assert (= (select RAND #b00000001) true))
(assert (= (select RAND #b00001000) true))
; Do the Intersection Operation
;(define-fun ToRANDArray ((ind s) (2D_array Set)) Res 
;(forall ((ind_1 s) (ind_2 s) (2d_array Set) (1d_array Res))
;(=> (and (= ind_2 ind) (= 2d_array 2D_array)) (= (select 2d_array ind_1 ind_2) (select 1d_array ind_2)))) 1d_array)

; "Intersection" Operation
(define-fun set_intersect ((x Res) (y Res)) Res ((_ map and) x y))
(define-fun IsEmpty ((x Res)) bool
(forall ((ind s) (x_in Res)) (and (= x_in x) (not (select x_in ind))))
)

; "Diff" Op : xor x ^ y = (~x & y) | (x & ~y) 
; "Diff" x\y = x & (x ^ y)
(define-fun set_diff ((x Res) (y Res)) Res
((_ map and) x ((_ map or) ((_ map and) ((_ map not) x) y) ((_ map and) x ((_ map not) y))))
)

;(define-fun IsEmpty ((x Res)) bool
;(forall ((ind s) (x_in Res)) (=> (and (= x_in x)) (not (select x_in ind))))
;)

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
