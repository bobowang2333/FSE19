(set-option :fixedpoint.engine datalog)
; this sort is used to define all the relations
(define-sort s () (_ BitVec 8))
(define-sort BitSet () (_ BitVec 4))
(define-sort ind () (_ BitVec 8))
(define-sort Set () (Array s bool))

;; Another method for encoding
;; DOM(R) = {0 0 1 0}
;; s = 1
;; dom(1, #b01) = true;
;; dom(1, #b11) = true;
;(declare-var R1 r)
;(declare-var R2 r)
;; to = from1 ^ from2
;(rule (=> (and dom(from1 R1) dom(from2 R1) (xor to from1) (xor to from2)) (dom(to R1)))) 
;; intersect(dom(s1, r) dom(s2, r))
;(declare-rel dom(s, r))

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
(declare-rel RAND_NUMBER (ind BitSet))
(declare-rel KEY_NUMBER (ind BitSet))
(declare-rel XOR_INCLUDE (s BitSet))
;; TEST
;; TEST: define the recursive relation
(declare-rel REC_RAND_VAR (s ind BitSet))
(declare-rel REC_ALL_INC (s ind BitSet))
(declare-rel Time (ind)) ;; define how many groups of 4-bit array

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
(declare-var int_bool2 bool)

;;; TEST
(declare-var x BitSet)
(declare-var y BitSet)
(declare-var z BitSet)

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
;; Define the recursive function
(declare-rel BVAND_REC (s s s ind))
(declare-rel BVAND_ALL_KEY_REC (s ind BitSet))
(declare-rel BVOR_RAND_REC (s s s ind))
(declare-rel BVOR_ALL_REC (s s s ind))
(declare-rel BV_INTERSECT_REC (s s ind BitSet))
(declare-rel INTERSECT_LABEL (s s))
(declare-rel BV_DIFF_REC (s s ind BitSet))
(declare-rel DIFF_LABEL (s s))
(declare-rel SET_SUM_REC (s s s ind))
(declare-rel XOR_RUD1_ALL_INC_REC (s s s ind))
(declare-rel BV_EQUAL_RAND_REC (s s ind))
(declare-rel BV_EQUAL_ALL_REC (s s ind))
(declare-rel BV_ZERO_REC (s s ind))
(declare-rel BV_IS_EMPTY_REC (s ind bool))
(declare-var X BitSet)
(declare-var Y BitSet)
(declare-var Z BitSet)
(declare-var X_A BitSet)
(declare-var Y_A BitSet)
(declare-var X_R BitSet)
(declare-var Y_R BitSet)
(declare-var N BitSet)
(declare-var Times ind)
(declare-var Times_New ind)
(declare-var Times_Past ind)
(declare-var time ind)
(declare-var var_x s)
(declare-var var_y s)
(declare-var var_z s)
(declare-var X_T BitSet)
(declare-var Y_T BitSet)
(declare-var Z_T BitSet)
(declare-var XY BitSet)
(declare-var XY_past BitSet)
(declare-var tmp BitSet)

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

; define the recursive;;;;;;;;;;;;;;;;
;;; TEST ;;;;;;;
(rule (REC_RAND_VAR #x66 #x01 #x1))
(rule (REC_RAND_VAR #x66 #x02 #x0))
(rule (REC_RAND_VAR #x67 #x01 #x2))
(rule (REC_RAND_VAR #x67 #x02 #x0))
(rule (REC_ALL_INC #x66 #x01 #x1))
(rule (REC_ALL_INC #x66 #x02 #x0))
(rule (REC_ALL_INC #x67 #x01 #x2))
(rule (REC_ALL_INC #x67 #x02 #x0))
;(rule (KEY_NUMBER #x1 #x8))
;(rule (KEY_NUMBER #x2 #x1))
(rule (assign #x68 #x66))
(rule (assign #x68 #x67))
;(rule (Time #x2))
;(rule (=> (and (assign to from1) (assign to from2)) (BVAND_REC from1 from2 to #x2)))
(rule (DIFF_LABEL #x66 #x67))
(rule (DIFF_LABEL #x67 #x66))
;(rule (=> (and (Time Times) (BV_IS_EMPTY_REC from1 Times int_bool0) (not int_bool0) (assign to from1)) (KEY_IND to)))
;(rule (=> (and (assign to from1) (assign to from2) (Time Times) (not (= from1 from2)) (BV_DIFF_REC from1 from2 Times int_res0) (DIFF_LABEL from1 from2) (BV_IS_EMPTY_REC var_x Times int_bool0) (not int_bool0)) (REC_RAND_VAR #x68 #x1 int_res0)))

;;;;;;;;;;;;;;;;;;;;;

;;; Define the rules ;;;;;
;; BV [AND] [RAND_VAR] ;; Times begin from "1"
(rule (=> (and (REC_RAND_VAR var_x Times X) (REC_RAND_VAR var_y Times Y) (BVAND_REC var_x var_y var_z Times) (= tmp (bvand X Y))) (REC_RAND_VAR var_z Times tmp)))
(rule (=> (and (BVAND_REC var_x var_y var_z Times) (not (= Times #x00)) (= Times_New (bvlshr Times #x01))) (BVAND_REC var_x var_y var_z Times_New)))
;; BV [AND] = [KEY] && [ALL_INC] ;;; for the [NO KEY] rule ;;;;;;
;(rule (=> (and (REC_ALL_INC var_x Times X) (KEY_NUMBER Times KEY_NUM) (BVAND X KEY_NUM int_res0) (= Times #x01)) (BVAND_ALL_KEY_REC var_x Times int_res0)))
;(rule (=> (and (BVAND_ALL_KEY_REC var_x Times_New int_res0) (REC_ALL_INC var_x Times X) (KEY_NUMBER Times KEY_NUM) (BVAND X KEY_NUM int_res1) (= Times_New (bvlshr Times #x01)) (not (= Times #x01)) (BVOR int_res0 int_res1 int_res2)) (BVAND_ALL_KEY_REC var_x Times int_res2)))
;; BV [OR] [RAND_VAR]
(rule (=> (and (REC_RAND_VAR var_x Times X) (REC_RAND_VAR var_y Times Y) (BVOR_RAND_REC var_x var_y var_z Times) (BVOR X Y XY)) (REC_RAND_VAR var_z Times XY)))
(rule (=> (and (BVOR_RAND_REC var_x var_y var_z Times) (not (= Times #x00)) (= Times_New (bvlshr Times #x01))) (BVOR_RAND_REC var_x var_y var_z Times_New)))
;; BV [OR] [ALL_INC]
(rule (=> (and (REC_ALL_INC var_x Times X) (REC_ALL_INC var_y Times Y) (BVOR_ALL_REC var_x var_y var_z Times) (BVOR X Y XY)) (REC_ALL_INC var_z Times XY)))
(rule (=> (and (BVOR_ALL_REC var_x var_y var_z Times) (not (= Times #x00)) (= Times_New (bvlshr Times #x01))) (BVOR_ALL_REC var_x var_y var_z Times_New)))
;; BV [Intersect] [ALL_INC]
(rule (=> (and (REC_ALL_INC var_x Times X) (REC_ALL_INC var_y Times Y) (= Times #x01) (BV_Intersect X Y XY)(INTERSECT_LABEL var_x var_y)) (BV_INTERSECT_REC var_x var_y Times XY)))
(rule (=> (and (REC_RAND_VAR var_x Times X) (REC_ALL_INC var_y Times Y) (not (= Times #x01)) (BV_Intersect X Y XY) (INTERSECT_LABEL var_x var_y) (= Times_New (bvlshr Times #x01)) (BV_INTERSECT_REC var_x var_y Times_New XY_past) (BVOR XY XY_past int_res0)) (BV_INTERSECT_REC var_x var_y Times int_res0)))
;; BV [DIFF] [RAND_VAR]\[ALL_INC]
(rule (=> (and (REC_RAND_VAR var_x Times X) (REC_ALL_INC var_y Times Y) (= Times #x01) (BV_Diff X Y XY) (DIFF_LABEL var_x var_y)) (BV_DIFF_REC var_x var_y Times XY)))
(rule (=> (and (REC_RAND_VAR var_x Times X) (REC_ALL_INC var_y Times Y) (not (= Times #x01)) (BV_Diff X Y XY) (DIFF_LABEL var_x var_y) (= Times_New (bvlshr Times #x01)) (BV_DIFF_REC var_x var_y Times_New XY_past) (BVOR XY XY_past int_res0)) (BV_DIFF_REC var_x var_y Times int_res0)))
;; BV [SET_SUM] [RAND_VAR] [RAND_VAR]
(rule (=> (and (REC_RAND_VAR var_x Times X) (REC_RAND_VAR var_y Times Y) (SET_SUM_REC var_x var_y var_z Times) (SET_SUM X Y XY)) (REC_RAND_VAR var_z Times XY)))
(rule (=> (and (SET_SUM_REC var_x var_y var_z Times) (not (= Times_New #x00)) (= Times_New (bvlshr Times #x01))) (SET_SUM_REC var_x var_y var_z Times_New)))
;; BV [XOR_RUD1_ALL_INC_REC] => generate the ALL_INC
(rule (=> (and (REC_RAND_VAR var_x Times X_R) (REC_RAND_VAR var_y Times Y_R) (REC_ALL_INC var_x Times X_A) (REC_ALL_INC var_y Times Y_A) (RAND_NUMBER Times RAND_NUM) (XOR_RUD1_ALL_INC X_A Y_A X_R Y_R RAND_NUM XY) (XOR_RUD1_ALL_INC_REC var_x var_y var_z Times)) (REC_ALL_INC var_z Times XY)))
(rule (=> (and (XOR_RUD1_ALL_INC_REC var_x var_y var_z Times) (= Times_New (bvlshr Times #x01)) (not (= Times_New #x00))) (XOR_RUD1_ALL_INC_REC var_x var_y var_z Times_New)))
;; BV [BV_EQUAL] ;; generate the same bit vector [RAND_VAR] => [RAND_VAR]
(rule (=> (and (REC_RAND_VAR var_x Times X) (BV_EQUAL_RAND_REC var_x var_y Times)) (REC_RAND_VAR var_y Times X)))
(rule (=> (and (BV_EQUAL_RAND_REC var_x var_y Times) (= Times_New (bvlshr Times #x01)) (not (= Times_New #x00))) (BV_EQUAL_RAND_REC var_x var_y Times_New)))
;; BV [BV_EQUAL] ;; [ALL_INC] => [ALL_INC]
(rule (=> (and (REC_ALL_INC var_x Times X) (BV_EQUAL_ALL_REC var_x var_y Times)) (REC_ALL_INC var_y Times X)))
(rule (=> (and (BV_EQUAL_ALL_REC var_x var_y Times) (= Times_New (bvlshr Times #x01)) (not (= Times_New #x00))) (BV_EQUAL_ALL_REC var_x var_y Times_New)))
;; BV [BV_ZERO] ;; [RAND]
(rule (=> (and (REC_RAND_VAR var_x Times X) (BV_ZERO_REC var_x var_y Times) (= XY #x0)) (REC_RAND_VAR var_y Times XY)))
(rule (=> (and (BV_ZERO_REC var_x var_y Times) (= Times_New (bvlshr Times #x01)) (not (= Times_New #x00))) (BV_ZERO_REC var_x var_y Times_New)))
;; BV [IS EMPTY] [RAND_VAR] ;;;; for the [NO KEY] rule
;(rule (=> (and (REC_RAND_VAR var_x Times X) (= Times #x01) (ISEMPTY X int_bool0)) (BV_IS_EMPTY_REC var_x Times int_bool0)))
;(rule (=> (and (REC_RAND_VAR var_x Times X) (ISEMPTY X int_bool0) (not (= Times #x01)) (= Times_New (bvlshr Times #x01)) (BV_IS_EMPTY_REC var_x Times_New int_bool1)) (BV_IS_EMPTY_REC var_x Times (and int_bool0 int_bool1))))

;; TEST
;(query KEY_IND :print-answer true)

;(rule (=> (and (> Times 1) (REC_RAND_VAR var_x Times X) (REC_RAND_VAR var_y Times Y) (bvand X_T Y_T XY) (BVAND_REC var_x var_y var_z (- Times 1) tmp)) (BVAND_REC var_x var_y var_z Times XY))))
;(rule (=> (BVAND_REC var_x var_y var_z Times XY) (REC_RAND_VAR var_z Times XY)))

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

; BitSet bitvector operation TEST;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; beginning of the [RULE] ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; rule: [XOR-RUD1] ;; left operand ;; [RAND] + [ANY]
;A => B, B can only be one clause, only A can use "and" to concatenate different clauses
;;; stratified definition about the negation (dom\semd == empty) ;;;;;;;;;
;; new recursive
(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (Time Times) (RAND from1)) (DIFF_LABEL from1 from2)))
(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (Time Times) (RAND from2)) (DIFF_LABEL from2 from1)))
(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (Time Times) (or (and (RAND from1) (BV_DIFF_REC from1 from2 Times int_res0) (not (= int_res0 #x0))) (and (RAND from2) (BV_DIFF_REC from2 from1 Times int_res1) (not (= int_res1 #x0))))) (RAND to)))
(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (Time Times) (and (and (RAND from1) (BV_DIFF_REC from1 from2 Times int_res0) (= int_res0 #x0)) (and (RAND from2) (BV_DIFF_REC from2 from1 Times int_res1) (= int_res1 #x0)))) (KEY_SENSITIVE to)))
(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (Time Times) (or (and (RAND from1) (BV_DIFF_REC from1 from2 Times int_res0) (not (= int_res0 #x0))) (and (RAND from2) (BV_DIFF_REC from2 from1 Times int_res1) (not (= int_res1 #x0))))) (SET_SUM_REC from1 from2 to Times)))
(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (Time Times) (and (and (RAND from1) (BV_DIFF_REC from1 from2 Times int_res0) (= int_res0 #x0)) (and (RAND from2) (BV_DIFF_REC from2 from1 Times int_res1) (= int_res1 #x0)))) (BV_ZERO_REC from1 to Times)))
; rule: [XOR_RUD1]
(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (Time Times) (or (RAND from1) (RAND from2))) (XOR_RUD1_ALL_INC_REC from1 from2 to Times)))


; rule [XOR] [KEY_SENSITIVE] + [KEY_SENSITIVE]
(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (KEY_SENSITIVE from1) (KEY_SENSITIVE from2)) (KEY_SENSITIVE to)))
(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (Time Times) (KEY_SENSITIVE from1) (KEY_SENSITIVE from2)) (BV_ZERO_REC from1 to Times)))
(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (Time Times) (KEY_SENSITIVE from1) (KEY_SENSITIVE from2)) (BVOR_ALL_REC from1 from2 to Times)))

; rule [XOR] [SID] + [SID] ;; TO DO: refinement ;; overlapping with rule [SID] 
(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (KEY_IND from1) (KEY_IND from2)) (INTERSECT_LABEL from1 from2)))
(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (KEY_IND from1) (KEY_IND from2) (Time Times) (BV_INTERSECT_REC from1 from2 Times int_res0) (= int_res0 #x0)) (KEY_IND to)))
(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (KEY_IND from1) (KEY_IND from2) (Time Times) (BV_INTERSECT_REC from1 from2 Times int_res0) (not (= int_res0 #x0))) (KEY_SENSITIVE to)))
;(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (KEY_IND from1) (KEY_IND from2) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (BVOR ALL_INC_A ALL_INC_B int_res0)) (ALL_INCLUDE to int_res0)))
(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (KEY_IND from1) (KEY_IND from2) (Time Times)) (BVOR_ALL_REC from1 from2 to Times)))
;(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (KEY_IND from1) (KEY_IND from2) (RAND_VAR from1 RAND_A) (BV_ZERO RAND_A int_res0))  (RAND_VAR to int_res0)))
(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (KEY_IND from1) (KEY_IND from2) (Time Times)) (BV_ZERO_REC from1 to Times)))

; rule [AO-RUD1] [RAND] + [NO_KEY] ;; left operand ;; ;;TYPE
;;;; change (not (KEY_SENSITIVE xxx)) = (or (IND) (RAND));;;;;;;

(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from1) (or (KEY_IND from2) (RAND from2))) (INTERSECT_LABEL from1 from2)))
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from1) (or (KEY_IND from2) (RAND from2)) (Time Times) (BV_INTERSECT_REC from1 from2 Times int_res0) (= int_res0 #x0)) (KEY_IND to)))
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from1) (or (KEY_IND from2) (RAND from2)) (Time Times) (BV_INTERSECT_REC from1 from2 Times int_res0) (not (= int_res0 #x0))) (KEY_SENSITIVE to)))
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from1) (or (KEY_IND from2) (RAND from2)) (Time Times)) (BVOR_ALL_REC from1 from2 to Times))) 
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from1) (or (KEY_IND from2) (RAND from2)) (Time Times)) (BV_ZERO_REC from1 to Times))) 

; rule [AO-RUD1] [RAND] + [KEY_SENSITIVE] ;; TYPE
;; left operand ;; constraint => ALL_INC_left /\ ALL_INC_right = empty 
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (KEY_SENSITIVE from2) (RAND from1)) (KEY_SENSITIVE to)))

; rule [AO-RUD1] ;; ARRAY
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (KEY_SENSITIVE from2) (RAND from1) (Time Times)) (BVOR_ALL_REC from1 from2 to Times)))
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (KEY_SENSITIVE from2) (RAND from1) (Time Times)) (BV_ZERO_REC from1 to Times)))

; rule [AO-RUD2] ;; right operand ;; [RAND] + [NO KEY] ;; TYPE
;;;; change (not (KEY_SENSITIVE xxx)) = (or (IND) (RAND));;;;;;;

(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from2) (or (KEY_IND from1) (RAND from1))) (INTERSECT_LABEL from1 from2)))
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (or (KEY_IND from1) (RAND from1)) (RAND from2) (Time Times) (BV_INTERSECT_REC from1 from2 Times int_res0) (= int_res0 #x0)) (KEY_IND to)))
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (or (KEY_IND from1) (RAND from1)) (RAND from2) (Time Times) (BV_INTERSECT_REC from1 from2 Times int_res0) (not (= int_res0 #x0))) (KEY_IND to)))
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (or (KEY_IND from1) (RAND from1)) (RAND from2) (Time Times)) (BVOR_ALL_REC from1 from2 to Times)))
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (or (KEY_IND from1) (RAND from1)) (RAND from2) (Time Times)) (BV_ZERO_REC from1 to Times)))

;rule [AO-RUD2] ;; right operand ;; [RAND] + [KEY_SENSITIVE]
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from2) (KEY_SENSITIVE from1)) (KEY_SENSITIVE to)))
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from2) (KEY_SENSITIVE from1) (Time Times)) (BVOR_ALL_REC from1 from2 to Times)))
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from2) (KEY_SENSITIVE from1) (Time Times)) (BV_ZERO_REC from1 to Times)))

; rule [AO-RUD3] ;;; TYPE
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from1) (RAND from2)) (DIFF_LABEL from1 from2)))
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from1) (RAND from2) (Time Times) (BV_DIFF_REC from1 from2 Times int_res0) (BV_DIFF_REC from2 from1 Times int_res1) (BVOR int_res0 int_res1 int_res2) (not (= int_res2 #x0))) (KEY_IND to)))
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from1) (RAND from2) (Time Times) (BV_DIFF_REC from1 from2 Times int_res0) (BV_DIFF_REC from2 from1 Times int_res1) (BVOR int_res0 int_res1 int_res2) (= int_res2 #x0)) (KEY_SENSITIVE to)))
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from1) (RAND from2) (Time Times)) (BVOR_ALL_REC from1 from2 to Times)))
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from1) (RAND from2) (Time Times)) (BV_ZERO_REC from1 to Times)))

; rule [AO] [KEY_SENSITIVE] + [KEY_SENSITIVE] ;; TYPE
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (KEY_SENSITIVE from1) (KEY_SENSITIVE from2)) (KEY_SENSITIVE to)))
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (KEY_SENSITIVE from1) (KEY_SENSITIVE from2) (Time Times)) (BVOR_ALL_REC from1 from2 to Times))) 
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (KEY_SENSITIVE from1) (KEY_SENSITIVE from2) (Time Times)) (BV_ZERO_REC from1 to Times))) 

; rule [SID] ;; AND OR  ;; TYPE [AO] +  [SID] + [SID]

(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (KEY_IND from1) (KEY_IND from2)) (INTERSECT_LABEL from1 from2)))
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (KEY_IND from1) (KEY_IND from2) (Time Times) (BV_INTERSECT_REC from1 from2 Times int_res0) (= int_res0 #x0)) (KEY_IND to)))
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (KEY_IND from1) (KEY_IND from2) (Time Times) (BV_INTERSECT_REC from1 from2 Times int_res0) (not (= int_res0 #x0))) (KEY_SENSITIVE to)))
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (KEY_IND from1) (KEY_IND from2) (Time Times)) (BVOR_ALL_REC from1 from2 to Times)))
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (KEY_IND from1) (KEY_IND from2) (Time Times)) (BV_ZERO_REC from1 to Times)))

; rule [NOT] RAND -> RAND
(rule (=> (and (not_assign to from1) (RAND from1)) (RAND to)))
(rule (=> (and (not_assign to from1)  (RAND from1) (Time Times)) (BV_EQUAL_RAND_REC from1 to Times))) 
(rule (=> (and (not_assign to from1) (RAND from1) (Time Times)) (BV_EQUAL_ALL_REC from1 to Times)))
; rule [NOT] SID -> SID
(rule (=> (and (not_assign to from1) (KEY_IND from1)) (KEY_IND to)))
(rule (=> (and (not_assign to from1) (KEY_IND from1) (Time Times)) (BV_EQUAL_RAND_REC from1 to Times)))
(rule (=> (and (not_assign to from1) (KEY_IND from1) (Time Times)) (BV_EQUAL_ALL_REC from1 to Times))) 
; rule [NOT] key_sensitive -> key_sensitive
(rule (=> (and (not_assign to from1) (KEY_SENSITIVE from1)) (KEY_SENSITIVE to)))
(rule (=> (and (not_assign to from1) (KEY_SENSITIVE from1) (Time Times)) (BV_EQUAL_RAND_REC from1 to Times))) 
(rule (=> (and (not_assign to from1) (KEY_SENSITIVE from1) (Time Times))(BV_EQUAL_ALL_REC from2 to Times)))

; rule [No KEY];; TO DO ;;; all the computation will have the decided types ;;; [NO KEY] rule is not necessary 
(rule (=> (CONSTANT from1) (KEY_IND from1)))
;(rule (=> (and (Time Times) (BVAND_ALL_KEY_REC from1 Times int_res0) (= int_res0 #x0) (BV_IS_EMPTY_REC from1 Times int_bool0) int_bool0) (KEY_IND from1)))

; rule [LOAD] + [KEY_SENSITIVE] 
(rule (=> (and (load_assign to from1) (KEY_SENSITIVE from1)) (KEY_SENSITIVE to)))
(rule (=> (and (load_assign to from1) (KEY_SENSITIVE from1) (Time Times)) (BV_EQUAL_ALL_REC from1 to Times)))
(rule (=> (and (load_assign to from1) (KEY_SENSITIVE from1) (Time Times)) (BV_EQUAL_RAND_REC from1 to Times)))

; rule [LOAD] + [KEY_IND]
(rule (=> (and (load_assign to from1) (KEY_IND from1)) (KEY_IND to)))
(rule (=> (and (load_assign to from1) (KEY_IND from1) (Time Times)) (BV_EQUAL_ALL_REC from1 to Times)))
(rule (=> (and (load_assign to from1) (KEY_IND from1) (Time Times)) (BV_EQUAL_RAND_REC from1 to Times)))

; rule [LOAD] + [RAND]
(rule (=> (and (load_assign to from1) (RAND from1)) (RAND to)))
(rule (=> (and (load_assign to from1) (RAND from1) (Time Times)) (BV_EQUAL_ALL_REC from1 to Times)))
(rule (=> (and (load_assign to from1) (RAND from1) (Time Times)) (BV_EQUAL_RAND_REC from1 to Times)))

; rule [STORE] + [KEY_SENSITIVE]
(rule (=> (and (store_assign to from1) (KEY_SENSITIVE from1)) (KEY_SENSITIVE to)))
(rule (=> (and (store_assign to from1) (KEY_SENSITIVE from1) (Time Times)) (BV_EQUAL_ALL_REC from1 to Times)))
(rule (=> (and (store_assign to from1) (KEY_SENSITIVE from1) (Time Times)) (BV_EQUAL_RAND_REC from1 to Times)))

; rule [STORE] + [KEY_IND]
(rule (=> (and (store_assign to from1) (KEY_IND from1)) (KEY_IND to)))
(rule (=> (and (store_assign to from1) (KEY_IND from1) (Time Times)) (BV_EQUAL_ALL_REC from1 to Times)))
(rule (=> (and (store_assign to from1) (KEY_IND from1) (Time Times)) (BV_EQUAL_RAND_REC from1 to Times)))

; rule [STORE] + [RAND]
(rule (=> (and (store_assign to from1) (RAND from1)) (RAND to)))
(rule (=> (and (store_assign to from1) (RAND from1) (Time Times)) (BV_EQUAL_ALL_REC from1 to Times)))
(rule (=> (and (store_assign to from1) (RAND from1) (Time Times)) (BV_EQUAL_RAND_REC from1 to Times)))


; specify the Times
(rule (Time #x80))
;; RAND_NUMBER
(rule (RAND_NUMBER #x01 #b0111))
(rule (RAND_NUMBER #x02 #b0000))
(rule (RAND_NUMBER #x04 #b0000))
(rule (RAND_NUMBER #x08 #b0000))
(rule (RAND_NUMBER #x10 #b0000))
(rule (RAND_NUMBER #x20 #b0000))
(rule (RAND_NUMBER #x40 #b0000))
(rule (RAND_NUMBER #x80 #b0000))
(rule (KEY_NUMBER #x01 #b1000))
(rule (KEY_NUMBER #x02 #b0000))
(rule (KEY_NUMBER #x04 #b0000))
(rule (KEY_NUMBER #x08 #b0000))
(rule (KEY_NUMBER #x10 #b0000))
(rule (KEY_NUMBER #x20 #b0000))
(rule (KEY_NUMBER #x40 #b0000))
(rule (KEY_NUMBER #x80 #b0000))
; user specify the sensitive variable
(rule (KEY_SENSITIVE #b00000100))
;(rule (KEY_NUMBER #b1000)) ; #b1000
(rule (REC_RAND_VAR #b00000100 #x01 #b0000))
(rule (REC_RAND_VAR #b00000100 #x02 #b0000))
(rule (REC_RAND_VAR #b00000100 #x04 #b0000))
(rule (REC_RAND_VAR #b00000100 #x08 #b0000))
(rule (REC_RAND_VAR #b00000100 #x10 #b0000))
(rule (REC_RAND_VAR #b00000100 #x20 #b0000))
(rule (REC_RAND_VAR #b00000100 #x40 #b0000))
(rule (REC_RAND_VAR #b00000100 #x80 #b0000))
(rule (REC_ALL_INC #b00000100 #x01 #b1000))
(rule (REC_ALL_INC #b00000100 #x02 #b0000))
(rule (REC_ALL_INC #b00000100 #x04 #b0000))
(rule (REC_ALL_INC #b00000100 #x08 #b0000))
(rule (REC_ALL_INC #b00000100 #x10 #b0000))
(rule (REC_ALL_INC #b00000100 #x20 #b0000))
(rule (REC_ALL_INC #b00000100 #x40 #b0000))
(rule (REC_ALL_INC #b00000100 #x80 #b0000))
; all the key value occupied bit are all "1"

;(rule (RAND #b00000001))
(rule (RAND #b00000001))
(rule (REC_RAND_VAR #b00000001 #x01 #b0001))
(rule (REC_RAND_VAR #b00000001 #x02 #b0000))
(rule (REC_RAND_VAR #b00000001 #x04 #b0000))
(rule (REC_RAND_VAR #b00000001 #x08 #b0000))
(rule (REC_RAND_VAR #b00000001 #x10 #b0000))
(rule (REC_RAND_VAR #b00000001 #x20 #b0000))
(rule (REC_RAND_VAR #b00000001 #x40 #b0000))
(rule (REC_RAND_VAR #b00000001 #x80 #b0000))
(rule (REC_ALL_INC #b00000001 #x01 #b0001))
(rule (REC_ALL_INC #b00000001 #x02 #b0000))
(rule (REC_ALL_INC #b00000001 #x04 #b0000))
(rule (REC_ALL_INC #b00000001 #x08 #b0000))
(rule (REC_ALL_INC #b00000001 #x10 #b0000))
(rule (REC_ALL_INC #b00000001 #x20 #b0000))
(rule (REC_ALL_INC #b00000001 #x40 #b0000))
(rule (REC_ALL_INC #b00000001 #x80 #b0000))
(rule (RAND #b00000010))
(rule (REC_RAND_VAR #b00000010 #x01 #b0010))
(rule (REC_RAND_VAR #b00000010 #x02 #b0000))
(rule (REC_RAND_VAR #b00000010 #x04 #b0000))
(rule (REC_RAND_VAR #b00000010 #x08 #b0000))
(rule (REC_RAND_VAR #b00000010 #x10 #b0000))
(rule (REC_RAND_VAR #b00000010 #x20 #b0000))
(rule (REC_RAND_VAR #b00000010 #x40 #b0000))
(rule (REC_RAND_VAR #b00000010 #x80 #b0000))
(rule (REC_ALL_INC #b00000010 #x01 #b0010))
(rule (REC_ALL_INC #b00000010 #x02 #b0000))
(rule (REC_ALL_INC #b00000010 #x04 #b0000))
(rule (REC_ALL_INC #b00000010 #x08 #b0000))
(rule (REC_ALL_INC #b00000010 #x10 #b0000))
(rule (REC_ALL_INC #b00000010 #x20 #b0000))
(rule (REC_ALL_INC #b00000010 #x40 #b0000))
(rule (REC_ALL_INC #b00000010 #x80 #b0000))
(rule (RAND #b00000011))
(rule (REC_RAND_VAR #b00000011 #x01 #b0100))
(rule (REC_RAND_VAR #b00000011 #x02 #b0000))
(rule (REC_RAND_VAR #b00000011 #x04 #b0000))
(rule (REC_RAND_VAR #b00000011 #x08 #b0000))
(rule (REC_RAND_VAR #b00000011 #x10 #b0000))
(rule (REC_RAND_VAR #b00000011 #x20 #b0000))
(rule (REC_RAND_VAR #b00000011 #x40 #b0000))
(rule (REC_RAND_VAR #b00000011 #x80 #b0000))
(rule (REC_ALL_INC #b00000011 #x01 #b0100))
(rule (REC_ALL_INC #b00000011 #x02 #b0000))
(rule (REC_ALL_INC #b00000011 #x04 #b0000))
(rule (REC_ALL_INC #b00000011 #x08 #b0000))
(rule (REC_ALL_INC #b00000011 #x10 #b0000))
(rule (REC_ALL_INC #b00000011 #x20 #b0000))
(rule (REC_ALL_INC #b00000011 #x40 #b0000))
(rule (REC_ALL_INC #b00000011 #x80 #b0000))
; if there are 3 random varibles RAND_NUM = #b0000_0111
;(rule (RAND_NUMBER #b0111))
; RAND_VAR (varID + bool_array(bitVector))
; ALL_INCLUDE (varID + bool_array (representing all variables r0, r1, ... k0, k1...))

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

(query KEY_IND :print-answer true)
