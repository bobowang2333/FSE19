(set-option :fixedpoint.engine datalog)
; this sort is used to define all the relations
(define-sort s () (_ BitVec 8))
(define-sort BitSet () (_ BitVec 4))
(define-sort Set () (Array s bool))

; assignment (assign from to)
(declare-rel assign(s s))
(declare-rel xor_assign_left (s s))
(declare-rel xor_assign_right (s s))
(declare-rel andor_assign_left (s s))
(declare-rel andor_assign_right (s s))
(declare-rel not_assign (s s))
(declare-rel load_assign (s s))
(declare-rel store_assign (s s))

; TDEP relation: (TDEP xxx, xxx)
(declare-rel TDEP (s s))
; KEY_SENSITIVE relation: KEY_SENSITIVE(var)
(declare-rel KEY_SENSITIVE (s))
(declare-rel KEY_IND (s))
(declare-rel CONSTANT (s))
(declare-rel RAND (s))
; define how many random variables here (user specified)
(declare-rel RAND_NUMBER (BitSet))
(declare-rel KEY_NUMBER (BitSet))
(declare-rel RAND_VAR (s BitSet))
(declare-rel ALL_INCLUDE (s BitSet))
(declare-rel XOR_INCLUDE (s BitSet))
;; TEST
(declare-rel XOR_AND (BitSet BitSet BitSet))

(declare-var var s)
(declare-var prev s)
(declare-var to s)
(declare-var from s)
(declare-var from1 s)
(declare-var from2 s)
(declare-var RAND_A BitSet)
(declare-var RAND_B BitSet)
(declare-var RAND_C BitSet)
(declare-var ALL_INC_A BitSet)
(declare-var ALL_INC_B BitSet)
(declare-var ALL_INC_C BitSet)

(declare-var RAND_NUM BitSet)
(declare-var KEY_NUM BitSet)
;; the intermediate result used in the rule
(declare-var int_res0 BitSet)
(declare-var int_res1 BitSet)
(declare-var int_res2 BitSet)
(declare-var int_bool0 bool)
(declare-var int_bool1 bool)

;;; TEST
(declare-var x BitSet)
(declare-var y BitSet)
(declare-var z BitSet)


; set theory operation define (on bitVectors)
; "Diff" Op: xor x ^ y = (~x & y) | (x & ~y)
; "Diff" x\y = x & (x ^ y)
(define-fun set_diff ((x BitSet) (y BitSet)) BitSet
(bvand x (bvor (bvand (bvnot x) y) (bvand x (bvnot y))))
)

(define-fun set_intersect ((x BitSet) (y BitSet)) BitSet
(bvand x y)
)

;for 8-bit vector 
(define-fun IsEmpty ((x BitSet)) bool
(= x #x0)
)

(define-fun set_or ((x BitSet) (y BitSet)) BitSet
(bvor x y)
)

(define-fun set_and ((x BitSet) (y BitSet)) BitSet
(bvand x y)
)

(define-fun set_no ((x BitSet)) BitSet
(bvnot x)
)
; res = (x | y) - (x & y) = x ^ y
(define-fun set_sum ((x BitSet) (y BitSet)) BitSet
(bvor (bvand x (bvnot y)) (bvand (bvnot x) y))
)

; ALL_INC(res) =( set_sum (rand_a, rand_b) or (not RAND_NUM)) and (RAND_A or RAND_B)
(define-fun xor_rud1_all_inc ((x_a BitSet) (y_a BitSet) (n BitSet)) BitSet
(bvand (bvor x_a y_a) (bvor (bvor (bvand x_a (bvnot y_a)) (bvand (bvnot x_a) y_a)) (bvnot n)))
)

;; TEST
(declare-fun test_bvand (BitSet BitSet) BitSet)
(assert (forall ((x BitSet) (y BitSet)) (= (test_bvand x y) (bvand x y))))

;; TEST
(declare-rel BVAND (BitSet BitSet BitSet))
(declare-rel BVOR (BitSet BitSet BitSet))
(declare-rel BVNOT (BitSet BitSet))
(declare-rel BV_Intersect (BitSet BitSet BitSet))
(declare-rel BV_Diff (BitSet BitSet BitSet))
(declare-rel ISEMPTY (BitSet bool))
(declare-rel NOEMPTY (BitSet bool))
(declare-rel SET_SUM (BitSet BitSet BitSet))
(declare-rel XOR_RUD1_ALL_INC (BitSet BitSet BitSet BitSet BitSet BitSet))
(declare-rel BV_EQUAL (BitSet BitSet))
(declare-rel BV_ZERO (BitSet BitSet))
(declare-rel IsBitVector (BitSet))
(declare-var X BitSet)
(declare-var Y BitSet)
(declare-var Z BitSet)
(declare-var X_A BitSet)
(declare-var Y_A BitSet)
(declare-var X_R BitSet)
(declare-var Y_R BitSet)
(declare-var N BitSet)

; (rule (=> (and (IsBitVector X) (IsBitVector Y)) (BVOR X Y (bvor X Y))))
(rule (=> (and true true) (BVAND X Y (bvand X Y))))
(rule (=> (and true true) (BVOR X Y (bvor X Y))))
(rule (=> (and true true) (BVNOT X (bvnot X))))
(rule (=> (and true true) (BV_Intersect X Y (bvand X Y)))) 
(rule (=> (and true true) (BV_Diff X Y (bvand X (bvor (bvand X (bvnot Y)) (bvand (bvnot X) Y))))))
(rule (=> (and true true) (ISEMPTY X (= X #x0))))
(rule (=> (and true true) (SET_SUM X Y (bvor (bvand X (bvnot Y)) (bvand (bvnot X) Y)))))
(rule (=> (and true true) (XOR_RUD1_ALL_INC X_A Y_A X_R Y_R N (bvand (bvor X_A Y_A) (bvor (bvnot N) (bvor (bvand X_R (bvnot Y_R)) (bvand (bvnot X_R) Y_R)))))))
(rule (=> (and true true) (BV_EQUAL X X)))
(rule (=> (and true true) (BV_ZERO X (bvand #x0 X))))

; the TDEP relation defines what it transitively depends on
(rule (=> (assign to from) (TDEP to from)))
(rule (=> (xor_assign_left to from) (assign to from)))
(rule (=> (xor_assign_right to from) (assign to from)))
(rule (=> (andor_assign_left to from) (assign to from)))
(rule (=> (andor_assign_right to from) (assign to from)))
(rule (=> (not_assign to from) (assign to from)))
(rule (=> (load_assign to from) (assign to from)))
(rule (=> (store_assign to from) (assign to from)))

; transitive closure of its assignments
(rule (=> (and (assign to from) (TDEP from prev)) (TDEP to prev)))
; transitive closure of its assignments
;(rule (=> (and (assign to from) (KEY_SENSITIVE from)) (KEY_SENSITIVE to)))

; BitSet bitvector operation TEST;;
(rule (=> (XOR_AND x y z) (BVAND x y z)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; beginning of the [RULE] ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; rule: [XOR-RUD1] ;; left operand ;; [RAND] + [ANY]
;A => B, B can only be one clause, only A can use "and" to concatenate different clauses
;;; stratified definition about the negation (dom\semd == empty) ;;;;;;;;;
(declare-rel DOM_SEMD_EMPTY (BitSet BitSet BitSet))
(rule (=> (and (BV_Diff X Y Z) (= Z #x0)) (DOM_SEMD_EMPTY X Y Z)))
(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (RAND_NUMBER RAND_NUM) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (or (and (RAND from1) (BV_Diff RAND_A ALL_INC_B int_res0) (not (= int_res0 #x0))) (and (RAND from2) (BV_Diff RAND_B ALL_INC_A int_res1) (not (= int_res1 #x0))))) (RAND to)))
;;; (rule (=> (and (xor_assign to from1) (xor_assign to from2) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (RAND_VAR to RAND_C) (RAND_NUMBER RAND_NUM) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (ALL_INCLUDE to ALL_INC_C) (RAND from1) (not (DOM_SEMD_EMPTY RAND_A RAND_B RAND_C))) (RAND to)))
(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (RAND_NUMBER RAND_NUM) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (and (and (RAND from1) (BV_Diff RAND_A ALL_INC_B int_res0) (= int_res0 #x0)) (and (RAND from2) (BV_Diff RAND_B ALL_INC_A int_res1) (= int_res1 #x0)))) (KEY_SENSITIVE to)))
; rule: [XOR_RUD1]
(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (RAND_NUMBER RAND_NUM) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (or (and (RAND from1) (BV_Diff RAND_A ALL_INC_B int_res0) (not (= int_res0 #x0))) (and (RAND from2) (BV_Diff RAND_B ALL_INC_A int_res1) (not (= int_res1 #x0)))) (SET_SUM RAND_A RAND_B int_res2)) (RAND_VAR to int_res2)))
(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (RAND_NUMBER RAND_NUM) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (and (and (RAND from1) (BV_Diff RAND_A ALL_INC_B int_res0) (= int_res0 #x0)) (and (RAND from2) (BV_Diff RAND_B ALL_INC_A int_res1) (= int_res1 #x0))) (BV_ZERO RAND_A int_res2)) (RAND_VAR to int_res2)))
; rule: [XOR_RUD1]
(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (RAND_NUMBER RAND_NUM) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (or (RAND from1) (RAND from2)) (XOR_RUD1_ALL_INC ALL_INC_A ALL_INC_B RAND_A RAND_B RAND_NUM int_res0)) (ALL_INCLUDE to int_res0)))

; rule: [XOR_RUD2] ;; right operand ;; [RAND] + [ANY]
;(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (RAND_NUMBER RAND_NUM) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (RAND from2) (BV_Diff RAND_B ALL_INC_A int_res0) (not (= int_res0 #b0000))) (RAND to)))
;(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (RAND_NUMBER RAND_NUM) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B)  (RAND from2) (BV_Diff RAND_B ALL_INC_A int_res0) (= int_res0 #b0000)) (KEY_SENSITIVE to)))
; rule: [XOR_RUD2]
;(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (RAND_NUMBER RAND_NUM) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (RAND from2) (BV_Diff RAND_B ALL_INC_A int_res0) (not (= int_res0 #b0000)) (SET_SUM RAND_A RAND_B int_res1)) (RAND_VAR to int_res1)))
;(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (RAND_NUMBER RAND_NUM) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (RAND from2) (BV_Diff RAND_B ALL_INC_A int_res0) (= int_res0 #b0000)) (RAND_VAR to #b0000)))
; rule: [XOR_RUD2]
;(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (RAND_NUMBER RAND_NUM) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (RAND from2) (XOR_RUD1_ALL_INC ALL_INC_A ALL_INC_B RAND_A RAND_B RAND_NUM int_res0)) (ALL_INCLUDE to int_res0)))

; rule [XOR] [KEY_SENSITIVE] + [KEY_SENSITIVE]
(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (KEY_SENSITIVE from1) (KEY_SENSITIVE from2)) (KEY_SENSITIVE to)))
(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (KEY_SENSITIVE from1) (KEY_SENSITIVE from2) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (BV_ZERO RAND_A int_res0)) (RAND_VAR to int_res0)))
(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (KEY_SENSITIVE from1) (KEY_SENSITIVE from2) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (BVOR ALL_INC_A ALL_INC_B int_res0)) (ALL_INCLUDE to int_res0)))

; rule [XOR] [SID] + [SID] ;; TO DO: refinement ;; overlapping with rule [SID] 
(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (KEY_IND from1) (KEY_IND from2) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (BV_Intersect ALL_INC_A ALL_INC_B int_res0) (= int_res0 #x0)) (KEY_IND to)))
(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (KEY_IND from1) (KEY_IND from2) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (BV_Intersect ALL_INC_A ALL_INC_B int_res0) (not (= int_res0 #x0))) (KEY_SENSITIVE to)))
(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (KEY_IND from1) (KEY_IND from2) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (BVOR ALL_INC_A ALL_INC_B int_res0)) (ALL_INCLUDE to int_res0)))
(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (KEY_IND from1) (KEY_IND from2) (RAND_VAR from1 RAND_A) (BV_ZERO RAND_A int_res0))  (RAND_VAR to int_res0)))

; rule [AO-RUD1] [RAND] + [NO_KEY] ;; left operand ;; ;;TYPE
;;;; change (not (KEY_SENSITIVE xxx)) = (or (IND) (RAND));;;;;;;
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (or (KEY_IND from2) (RAND from2)) (RAND from1) (BV_Intersect ALL_INC_A ALL_INC_B int_res0) (= int_res0 #x0)) (KEY_IND to))) 
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (or (KEY_IND from2) (RAND from2)) (RAND from1) (BV_Intersect ALL_INC_A ALL_INC_B int_res0) (not (= int_res0 #x0))) (KEY_SENSITIVE to))) 
; rule [AO-RUD1] ;; ARRAY
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (RAND from1) (or (RAND from2) (KEY_IND from2)) (BVOR ALL_INC_A ALL_INC_B int_res1)) (ALL_INCLUDE to int_res1)))
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (RAND from1) (or (RAND from2) (KEY_IND from2)) (BV_ZERO RAND_A int_res1)) (RAND_VAR to int_res1)))

; rule [AO-RUD1] [RAND] + [KEY_SENSITIVE] ;; TYPE
;; left operand ;; constraint => ALL_INC_left /\ ALL_INC_right = empty 
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (KEY_SENSITIVE from2) (RAND from1)) (KEY_SENSITIVE to)))
; rule [AO-RUD1] ;; ARRAY
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (KEY_SENSITIVE from2) (RAND from1) (BVOR ALL_INC_A ALL_INC_B int_res0)) (ALL_INCLUDE to int_res0)))
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (KEY_SENSITIVE from2) (RAND from1) (BV_ZERO RAND_A int_res0)) (RAND_VAR to int_res0)))


; rule [AO-RUD2] ;; right operand ;; [RAND] + [NO KEY] ;; TYPE
;;;; change (not (KEY_SENSITIVE xxx)) = (or (IND) (RAND));;;;;;;
;(rule (=> (and (andor_assign to from1) (andor_assign to from2) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (RAND_VAR to RAND_C) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (ALL_INCLUDE to ALL_INC_C) (not (KEY_SENSITIVE from1)) (RAND from2) (BV_Intersect ALL_INC_A ALL_INC_B int_res0) (ISEMPTY int_res0 int_bool0) int_bool0) (KEY_IND to)))
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (or (KEY_IND from1) (RAND from1)) (RAND from2) (BV_Intersect ALL_INC_A ALL_INC_B int_res0)  (= int_res0 #x0)) (KEY_IND to)))
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (or (KEY_IND from1) (RAND from1)) (RAND from2) (BV_Intersect ALL_INC_A ALL_INC_B int_res0) (not (= int_res0 #x0))) (KEY_SENSITIVE to)))
; rule [AO-RUD2] ;; ARRAY
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (RAND from2) (or (RAND from1) (KEY_IND from1)) (BVOR ALL_INC_A ALL_INC_B int_res1)) (ALL_INCLUDE to int_res1)))
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (RAND from2) (or (RAND from1) (KEY_IND from1)) (BV_ZERO RAND_B int_res1)) (RAND_VAR to int_res1)))

;rule [AO-RUD2] ;; right operand ;; [RAND] + [KEY_SENSITIVE]
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (KEY_SENSITIVE from1) (RAND from2)) (KEY_SENSITIVE to)))
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (KEY_SENSITIVE from1) (RAND from2) (BVOR ALL_INC_A ALL_INC_B int_res0)) (ALL_INCLUDE to int_res0)))
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (KEY_SENSITIVE from1) (RAND from2) (BV_ZERO RAND_A int_res0)) (RAND_VAR to int_res0)))

; rule [AO-RUD3] ;;; TYPE
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (RAND from1) (RAND from2) (BV_Diff RAND_A ALL_INC_B int_res0) (BV_Diff RAND_B ALL_INC_A int_res1) (BVOR int_res0 int_res1 int_res2) (not (= int_res2 #x0))) (KEY_IND to)))
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (RAND from1) (RAND from2) (BV_Diff RAND_A ALL_INC_B int_res0) (BV_Diff RAND_B ALL_INC_A int_res1) (BVOR int_res0 int_res1 int_res2) (= int_res2 #x0)) (KEY_SENSITIVE to)))
; rule [AO-RUD3] ;;; ARRAY
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (RAND from1) (RAND from2) (BVOR ALL_INC_A ALL_INC_B int_res0)) (ALL_INCLUDE to int_res0)))
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (RAND from1) (RAND from2) (BV_ZERO RAND_A int_res0)) (RAND_VAR to int_res0)))

; rule [AO] [KEY_SENSITIVE] + [KEY_SENSITIVE] ;; TYPE
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (KEY_SENSITIVE from1) (KEY_SENSITIVE from2) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B)) (KEY_SENSITIVE to)))
; rule [AO] [KEY_SENSITIVE] + [KEY_SENSITIVE] ;; ARRAY
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (KEY_SENSITIVE from1) (KEY_SENSITIVE from2) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (BVOR ALL_INC_A ALL_INC_B int_res0)) (ALL_INCLUDE to int_res0)))
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (KEY_SENSITIVE from1) (KEY_SENSITIVE from2) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (BV_ZERO RAND_A int_res0)) (RAND_VAR to int_res0)))

; rule [SID] ;; AND OR  ;; TYPE [AO] +  [SID] + [SID]
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (KEY_IND from1) (KEY_IND from2) (BV_Intersect ALL_INC_A ALL_INC_B int_res0) (= int_res0 #x0)) (KEY_IND to)))
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (KEY_IND from1) (KEY_IND from2) (BV_Intersect ALL_INC_A ALL_INC_B int_res0) (not (= int_res0 #x0))) (KEY_SENSITIVE to)))
; rule [SID] ;; [AO] + [SID] + [SID] ;; ARRAY
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (KEY_IND from1) (KEY_IND from2) (BVOR ALL_INC_A ALL_INC_B int_res1)) (ALL_INCLUDE to int_res1)))
(rule (=> (and (assign to from1) (assign to from2) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (KEY_IND from1) (KEY_IND from2) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (BV_ZERO RAND_A int_res0)) (RAND_VAR to int_res0)))

; rule [NOT] RAND -> RAND
(rule (=> (and (not_assign to from1) (RAND from1)) (RAND to)))
(rule (=> (and (not_assign to from1) (RAND_VAR from1 RAND_A) (RAND from1)) (RAND_VAR to RAND_A)))
(rule (=> (and (not_assign to from1) (ALL_INCLUDE from1 ALL_INC_A) (RAND from1)) (ALL_INCLUDE to ALL_INC_A)))
; rule [NOT] SID -> SID
(rule (=> (and (not_assign to from1) (KEY_IND from1)) (KEY_IND to)))
(rule (=> (and (not_assign to from1) (ALL_INCLUDE from1 ALL_INC_A) (KEY_IND from1)) (ALL_INCLUDE to ALL_INC_A)))
(rule (=> (and (not_assign to from1) (RAND_VAR from1 RAND_A) (KEY_IND from1)) (RAND_VAR to RAND_A)))
; rule [NOT] key_sensitive -> key_sensitive
(rule (=> (and (not_assign to from1) (KEY_SENSITIVE from1)) (KEY_SENSITIVE to)))
(rule (=> (and (not_assign to from1) (ALL_INCLUDE from1 ALL_INC_A) (KEY_SENSITIVE from1)) (ALL_INCLUDE to ALL_INC_A)))
(rule (=> (and (not_assign to from1) (RAND_VAR from1 RAND_A) (KEY_SENSITIVE from1)) (RAND_VAR to RAND_A)))

; rule [No KEY]
(rule (=> (and (ALL_INCLUDE from1 ALL_INC_A) (KEY_NUMBER KEY_NUM) (BVAND ALL_INC_A KEY_NUM int_res0) (ISEMPTY int_res0 int_bool0) int_bool0 (RAND_VAR from1 RAND_A) (= RAND_A #x0)) (KEY_IND from1)))
(rule (=> (CONSTANT from1) (KEY_IND from1)))

; rule [LOAD] + [KEY_SENSITIVE] 
(rule (=> (and (load_assign to from1) (KEY_SENSITIVE from1)) (KEY_SENSITIVE to)))
(rule (=> (and (load_assign to from1) (KEY_SENSITIVE from1) (ALL_INCLUDE from1 ALL_INC_A)) (ALL_INCLUDE to ALL_INC_A)))
(rule (=> (and (load_assign to from1) (KEY_SENSITIVE from1) (RAND_VAR from1 RAND_A) (BV_ZERO RAND_A int_res0)) (RAND_VAR to int_res0)))

; rule [LOAD] + [KEY_IND]
(rule (=> (and (load_assign to from1) (KEY_IND from1)) (KEY_IND to)))
(rule (=> (and (load_assign to from1) (KEY_IND from1) (ALL_INCLUDE from1 ALL_INC_A)) (ALL_INCLUDE to ALL_INC_A)))
(rule (=> (and (load_assign to from1) (KEY_IND from1) (RAND_VAR from1 RAND_A) (BV_EQUAL RAND_A int_res0)) (RAND_VAR to int_res0)))

; rule [LOAD] + [RAND]
(rule (=> (and (load_assign to from1) (RAND from1)) (RAND to)))
(rule (=> (and (load_assign to from1) (RAND from1) (ALL_INCLUDE from1 ALL_INC_A)) (ALL_INCLUDE to ALL_INC_A)))
(rule (=> (and (load_assign to from1) (RAND from1) (RAND_VAR from1 RAND_A)) (RAND_VAR to RAND_A)))

; rule [STORE] + [KEY_SENSITIVE]
(rule (=> (and (store_assign to from1) (KEY_SENSITIVE from1)) (KEY_SENSITIVE to)))
(rule (=> (and (store_assign to from1) (KEY_SENSITIVE from1) (ALL_INCLUDE from1 ALL_INC_A)) (ALL_INCLUDE to ALL_INC_A)))
(rule (=> (and (store_assign to from1) (KEY_SENSITIVE from1) (RAND_VAR from1 RAND_A) (BV_ZERO RAND_A int_res0)) (RAND_VAR to int_res0)))

; rule [STORE] + [KEY_IND]
(rule (=> (and (store_assign to from1) (KEY_IND from1)) (KEY_IND to)))
(rule (=> (and (store_assign to from1) (KEY_IND from1) (ALL_INCLUDE from1 ALL_INC_A)) (ALL_INCLUDE to ALL_INC_A)))
(rule (=> (and (store_assign to from1) (KEY_IND from1) (RAND_VAR from1 RAND_A)) (RAND_VAR to RAND_A)))

; rule [STORE] + [RAND]
(rule (=> (and (store_assign to from1) (RAND from1)) (RAND to)))
(rule (=> (and (store_assign to from1) (RAND from1) (ALL_INCLUDE from1 ALL_INC_A)) (ALL_INCLUDE to ALL_INC_A)))
(rule (=> (and (store_assign to from1) (RAND from1) (RAND_VAR from1 RAND_A)) (RAND_VAR to RAND_A)))

; Auxiliary Rules ;;;;;;; Overlapping with [XOR] rules listed above;;;;;;;;;;;;;
; XOR rule [KEY] with [RAND] ==> [RAND] (expressed in [XOR-RUD1])
; XOR rule [KEY] with [RAND] ==> [KEY] (left side)
;(rule (=> (and (xor_assign to from1) (xor_assign to from2) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (RAND_VAR to RAND_C) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (ALL_INCLUDE to ALL_INC_C) (KEY_SENSITIVE from1) (RAND from2) (BV_Diff RAND_B ALL_INC_A int_res0) (ISEMPTY int_res0 int_bool0) int_bool0) (KEY_SENSITIVE to)))
;(rule (=> (and (xor_assign to from1) (xor_assign to from2) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (RAND_VAR to RAND_C) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (ALL_INCLUDE to ALL_INC_C) (KEY_SENSITIVE from1) (RAND from2) (BV_Diff RAND_B ALL_INC_A int_res0) (ISEMPTY int_res0 int_bool0) int_bool0) (BVOR ALL_INC_A ALL_INC_B ALL_INC_C)))
; XOR rule [KEY] with [RAND] ==> [KEY] (right side)
;(rule (=> (and (xor_assign to from1) (xor_assign to from2) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (RAND_VAR to RAND_C) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (ALL_INCLUDE to ALL_INC_C) (KEY_SENSITIVE from2) (RAND from1) (BV_Diff RAND_A ALL_INC_B int_res0) (ISEMPTY int_res0 int_bool0) int_bool0) (KEY_SENSITIVE to)))
;(rule (=> (and (xor_assign to from1) (xor_assign to from2) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (RAND_VAR to RAND_C) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (ALL_INCLUDE to ALL_INC_C) (KEY_SENSITIVE from2) (RAND from1) (BV_Diff RAND_A ALL_INC_B int_res0) (ISEMPTY int_res0 int_bool0) int_bool0) (BVOR ALL_INC_A ALL_INC_B ALL_INC_C)))

; XOR rule [KEY] with [SID] ===> [KEY]
;(rule (=> (and (xor_assign to from1) (xor_assign to from2) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (ALL_INCLUDE to ALL_INC_C) (KEY_SENSITIVE from1) (KEY_IND from2)) (KEY_SENSITIVE to)))

; user specify the sensitive variable
(rule (KEY_SENSITIVE #b00000100))
(rule (KEY_NUMBER #b1000)) ; #b1000
(rule (RAND_VAR #b00000100 #b0000))
(rule (ALL_INCLUDE #b00000100 #b1000))
; all the key value occupied bit are all "1"

;(rule (RAND #b00000001))
(rule (RAND #b00000001))
(rule (RAND #b00000010))
(rule (RAND #b00000011))
; if there are 3 random varibles RAND_NUM = #b0000_0111
(rule (RAND_NUMBER #b0111))
; RAND_VAR (varID + bool_array(bitVector))
(rule (RAND_VAR #b00000001 #b0001))
(rule (RAND_VAR #b00000010 #b0010))
(rule (RAND_VAR #b00000011 #b0100))
; ALL_INCLUDE (varID + bool_array (representing all variables r0, r1, ... k0, k1...))
(rule (ALL_INCLUDE #b00000001 #b0001))
(rule (ALL_INCLUDE #b00000010 #b0010))
(rule (ALL_INCLUDE #b00000011 #b0100))

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
