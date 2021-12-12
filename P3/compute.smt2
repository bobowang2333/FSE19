(set-option :fixedpoint.engine datalog)
; this sort is used to define all the relations
(define-sort s () (_ BitVec 16))

(define-sort BitSet () (_ BitVec 4))
(define-sort ind () (_ BitVec 1))
; assignment (assign from to)
(declare-rel assign(s s))
(declare-rel TDEP (s s))
(declare-rel xor_assign_left (s s))
(declare-rel xor_assign_right (s s))
(declare-rel andor_assign_left (s s))
(declare-rel andor_assign_right (s s))
(declare-rel not_assign (s s))
(declare-rel load_assign (s s))
(declare-rel store_assign (s s))
(declare-rel zext_assign (s s))
(declare-rel icmp_assign (s s))
(declare-rel trunc_assign (s s))
(declare-rel share(s s))
(declare-rel binary_constant(s s))
(declare-rel equal_assign (s s))

; declare the types which are gonna be used
(declare-rel KEY_SENSITIVE (s))
(declare-rel KEY_IND (s))
(declare-rel CONSTANT (s))
(declare-rel RAND (s))
(declare-rel HD_SENSITIVE (s s))
(declare-rel HD_SENSITIVE_2 (s s))

; define the TYPE array
(declare-rel RAND_NUMBER (ind BitSet))
(declare-rel KEY_NUMBER (ind BitSet))
(declare-rel REC_RAND_VAR (s ind BitSet))
(declare-rel REC_ALL_INC (s ind BitSet))
(declare-rel Time (ind))

; declare varibles which are used to define the rules (type:s)
(declare-var var s)
(declare-var prev s)
(declare-var to s)
(declare-var from s)
(declare-var from1 s)
(declare-var from2 s)
(declare-var to_e s)
(declare-var from_e s)

; declare variables which are used (type: bitSet)
(declare-var RAND_A BitSet)
(declare-var RAND_B BitSet)
(declare-var RAND_C BitSet)
(declare-var ALL_INC_A BitSet)
(declare-var ALL_INC_B BitSet)
(declare-var ALL_INC_C BitSet)
(declare-var RAND_NUM BitSet)
(declare-var KEY_NUM BitSet)
(declare-var int_res0 BitSet)
(declare-var int_res1 BitSet)
(declare-var int_res2 BitSet)
(declare-var int_bool0 bool)
(declare-var int_bool1 bool)

; define the function which will be used in the rules
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

; define the recursive function used in the rules
(declare-rel BVAND_REC (s s s ind))
(declare-rel BVAND_ALL_KEY_REC (s ind BitSet))
(declare-rel BVOR_RAND_REC (s s s ind))
(declare-rel BVOR_ALL_REC (s s s ind))
(declare-rel BV_INTERSECT_REC (s s ind BitSet))
(declare-rel INTERSECT_LABEL (s s))
(declare-rel BV_DIFF_REC (s s ind BitSet))
(declare-rel DIFF_LABEL (s s))
(declare-rel BV_SAME_REC (s s ind BitSet))
(declare-rel CHECK_SAME (s s))
(declare-rel SET_SUM_REC (s s s ind))
(declare-rel XOR_RUD1_ALL_INC_REC (s s s ind))
(declare-rel BV_EQUAL_RAND_REC (s s ind))
(declare-rel BV_EQUAL_ALL_REC (s s ind))
(declare-rel BV_ZERO_REC (s s ind))
(declare-rel BV_IS_EMPTY_REC (s ind bool))

; define the variables used for the function
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

; define the functions
(rule (=> (and true true) (BVAND X Y (bvand X Y))))
(rule (=> (and true true) (BVOR X Y (bvor X Y))))
(rule (=> (and true true) (BVNOT X (bvnot X))))
(rule (=> (and true true) (BV_Intersect X Y (bvand X Y))))
(rule (=> (and true true) (BV_Diff X Y (bvand X (bvor (bvand X (bvnot Y)) (bvand (bvnot X) Y))))))
(rule (=> (and true true) (ISEMPTY X (= X #b0000))))
(rule (=> (and true true) (SET_SUM X Y (bvor (bvand X (bvnot Y)) (bvand (bvnot X) Y)))))
(rule (=> (and true true) (XOR_RUD1_ALL_INC X_A Y_A X_R Y_R N (bvand (bvor X_A Y_A) (bvor (bvnot N) (bvor (bvand X_R (bvnot Y_R)) (bvand (bvnot X_R) Y_R)))))))
(rule (=> (and true true) (BV_EQUAL X X)))
(rule (=> (and true true) (BV_ZERO X (bvand #b0000 X))))

; defining the recursive function ;;;;;;;
;; BV [AND] [RAND_VAR] ;; Times begin from 1 
(rule (=> (and (REC_RAND_VAR var_x Times X) (REC_RAND_VAR var_y Times Y) (BVAND_REC var_x var_y var_z Times) (= tmp (bvand X Y))) (REC_RAND_VAR var_z Times tmp)))
(rule (=> (and (BVAND_REC var_x var_y var_z Times) (not (= Times #b0)) (= Times_New (bvsub Times #b1))) (BVAND_REC var_x var_y var_z Times_New)))
;; BV [AND] = [KEY] && [ALL_INC] ;;; for the [NO KEY] rule ;;;;;;
;(rule (=> (and (REC_ALL_INC var_x Times X) (KEY_NUMBER Times KEY_NUM) (BVAND X KEY_NUM int_res0) (= Times #b1)) (BVAND_ALL_KEY_REC var_x Times int_res0)))
;(rule (=> (and (BVAND_ALL_KEY_REC var_x Times_New int_res0) (REC_ALL_INC var_x Times X) (KEY_NUMBER Times KEY_NUM) (BVAND X KEY_NUM int_res1) (= Times_New (bvsub Times #b1)) (not (= Times #b1)) (BVOR int_res0 int_res1 int_res2)) (BVAND_ALL_KEY_REC var_x Times int_res2)))
;; BV [OR] [RAND_VAR]
(rule (=> (and (REC_RAND_VAR var_x Times X) (REC_RAND_VAR var_y Times Y) (BVOR_RAND_REC var_x var_y var_z Times) (BVOR X Y XY)) (REC_RAND_VAR var_z Times XY)))
(rule (=> (and (BVOR_RAND_REC var_x var_y var_z Times) (not (= Times #b0)) (= Times_New (bvsub Times #b1))) (BVOR_RAND_REC var_x var_y var_z Times_New)))
;; BV [OR] [ALL_INC]
(rule (=> (and (REC_ALL_INC var_x Times X) (REC_ALL_INC var_y Times Y) (BVOR_ALL_REC var_x var_y var_z Times) (BVOR X Y XY)) (REC_ALL_INC var_z Times XY)))
(rule (=> (and (BVOR_ALL_REC var_x var_y var_z Times) (not (= Times #b0)) (= Times_New (bvsub Times #b1))) (BVOR_ALL_REC var_x var_y var_z Times_New)))
;; BV [Intersect] [ALL_INC]
(rule (=> (and (REC_ALL_INC var_x Times X) (REC_ALL_INC var_y Times Y) (= Times #b1) (BV_Intersect X Y XY)(INTERSECT_LABEL var_x var_y)) (BV_INTERSECT_REC var_x var_y Times XY)))
(rule (=> (and (REC_RAND_VAR var_x Times X) (REC_ALL_INC var_y Times Y) (not (= Times #b1)) (BV_Intersect X Y XY) (INTERSECT_LABEL var_x var_y) (= Times_New (bvsub Times #b1)) (BV_INTERSECT_REC var_x var_y Times_New XY_past) (BVOR XY XY_past int_res0)) (BV_INTERSECT_REC var_x var_y Times int_res0)))
;; BV [DIFF] [RAND_VAR][ALL_INC]
(rule (=> (and (REC_RAND_VAR var_x Times X) (REC_ALL_INC var_y Times Y) (= Times #b1) (BV_Diff X Y XY) (DIFF_LABEL var_x var_y)) (BV_DIFF_REC var_x var_y Times XY)))
(rule (=> (and (REC_RAND_VAR var_x Times X) (REC_ALL_INC var_y Times Y) (not (= Times #b1)) (BV_Diff X Y XY) (DIFF_LABEL var_x var_y) (= Times_New (bvsub Times #b1)) (BV_DIFF_REC var_x var_y Times_New XY_past) (BVOR XY XY_past int_res0)) (BV_DIFF_REC var_x var_y Times int_res0)))
;; BV [SAME] [ALL_INC] [ALL_INC]
(rule (=> (and (REC_ALL_INC var_x Times X) (REC_ALL_INC var_y Times Y) (= Times #b1) (SET_SUM X Y XY)(CHECK_SAME var_x var_y)) (BV_SAME_REC var_x var_y Times XY)))
(rule (=> (and (REC_ALL_INC var_x Times X) (REC_ALL_INC var_y Times Y) (not (= Times #b1)) (SET_SUM X Y XY) (CHECK_SAME var_x var_y) (= Times_New (bvsub Times #b1)) (BV_SAME_REC var_x var_y Times_New XY_past) (BVOR XY XY_past int_res0)) (BV_SAME_REC var_x var_y Times int_res0)))
;; BV [SET_SUM] [RAND_VAR] [RAND_VAR]
(rule (=> (and (REC_RAND_VAR var_x Times X) (REC_RAND_VAR var_y Times Y) (SET_SUM_REC var_x var_y var_z Times) (SET_SUM X Y XY)) (REC_RAND_VAR var_z Times XY)))
(rule (=> (and (SET_SUM_REC var_x var_y var_z Times) (not (= Times_New #b0)) (= Times_New (bvsub Times #b1))) (SET_SUM_REC var_x var_y var_z Times_New)))
;; BV [XOR_RUD1_ALL_INC_REC] => generate the ALL_INC
(rule (=> (and (REC_RAND_VAR var_x Times X_R) (REC_RAND_VAR var_y Times Y_R) (REC_ALL_INC var_x Times X_A) (REC_ALL_INC var_y Times Y_A) (RAND_NUMBER Times RAND_NUM) (XOR_RUD1_ALL_INC X_A Y_A X_R Y_R RAND_NUM XY) (XOR_RUD1_ALL_INC_REC var_x var_y var_z Times)) (REC_ALL_INC var_z Times XY)))
(rule (=> (and (XOR_RUD1_ALL_INC_REC var_x var_y var_z Times) (= Times_New (bvsub Times #b1)) (not (= Times_New #b0))) (XOR_RUD1_ALL_INC_REC var_x var_y var_z Times_New)))
;; BV [BV_EQUAL] ;; generate the same bit vector [RAND_VAR] => [RAND_VAR]
(rule (=> (and (REC_RAND_VAR var_x Times X) (BV_EQUAL_RAND_REC var_x var_y Times)) (REC_RAND_VAR var_y Times X)))
(rule (=> (and (BV_EQUAL_RAND_REC var_x var_y Times) (= Times_New (bvsub Times #b1)) (not (= Times_New #b0))) (BV_EQUAL_RAND_REC var_x var_y Times_New)))
;; BV [BV_EQUAL] ;; [ALL_INC] => [ALL_INC]
(rule (=> (and (REC_ALL_INC var_x Times X) (BV_EQUAL_ALL_REC var_x var_y Times)) (REC_ALL_INC var_y Times X)))
(rule (=> (and (BV_EQUAL_ALL_REC var_x var_y Times) (= Times_New (bvsub Times #b1)) (not (= Times_New #b0))) (BV_EQUAL_ALL_REC var_x var_y Times_New)))
;; BV [BV_ZERO] ;; [RAND]
(rule (=> (and (REC_RAND_VAR var_x Times X) (BV_ZERO_REC var_x var_y Times) (= XY #b0000)) (REC_RAND_VAR var_y Times XY)))
(rule (=> (and (BV_ZERO_REC var_x var_y Times) (= Times_New (bvsub Times #b1)) (not (= Times_New #b0))) (BV_ZERO_REC var_x var_y Times_New)))
;; BV [IS EMPTY] [RAND_VAR] ;;;; for the [NO KEY] rule
;(rule (=> (and (REC_RAND_VAR var_x Times X) (= Times #b1) (ISEMPTY X int_bool0)) (BV_IS_EMPTY_REC var_x Times int_bool0)))
;(rule (=> (and (REC_RAND_VAR var_x Times X) (ISEMPTY X int_bool0) (not (= Times #b1)) (= Times_New (bvsub Times #b1)) (BV_IS_EMPTY_REC var_x Times_New int_bool1)) (BV_IS_EMPTY_REC var_x Times (and int_bool0 int_bool1))))

; [RULE] define the assign relation
(rule (=> (assign to from) (TDEP to from)))
;(rule (=> (xor_assign_left to from) (assign to from)))
;(rule (=> (xor_assign_right to from) (assign to from)))
;(rule (=> (andor_assign_left to from) (assign to from)))
;(rule (=> (andor_assign_right to from) (assign to from)))
;(rule (=> (not_assign to from) (assign to from)))
(rule (=> (load_assign to from) (assign to from)))
(rule (=> (store_assign to from) (assign to from)))
; [RULE] transitive closure
(rule (=> (and (assign to from) (TDEP from prev)) (TDEP to prev)))

;;;;;;;;;;;;;;;;;;;;;;;;;; beginning of the [RULE] ;;;;;;;;;;;;;;;;;;;;
; rule: [XOR-RUD1] ;; left operand ;; [RAND] + [ANY]
;A => B, B can only be one clause, only A can use <and> to concatenate different clauses
;;new recursive
(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (Time Times) (RAND from1)) (DIFF_LABEL from1 from2)))
(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (Time Times) (RAND from2)) (DIFF_LABEL from2 from1)))
(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (Time Times) (or (and (RAND from1) (BV_DIFF_REC from1 from2 Times int_res0) (not (= int_res0 #b0000))) (and (RAND from2) (BV_DIFF_REC from2 from1 Times int_res1) (not (= int_res1 #b0000))))) (RAND to)))
(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (Time Times) (and (and (RAND from1) (BV_DIFF_REC from1 from2 Times int_res0) (= int_res0 #b0000)) (and (RAND from2) (BV_DIFF_REC from2 from1 Times int_res1) (= int_res1 #b0000)))) (CHECK_SAME from1 from2)))
(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (Time Times) (or (RAND from1) (RAND from2)) (BV_SAME_REC from1 from2 Times int_res0) (= int_res0 #b0000)) (KEY_IND to)))
(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (Time Times) (or (RAND from1) (RAND from2)) (BV_SAME_REC from1 from2 Times int_res0) (not (= int_res0 #b0000))) (KEY_SENSITIVE to)))
;; define the array for [RAND_VAR]
(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (Time Times) (or (and (RAND from1) (BV_DIFF_REC from1 from2 Times int_res0) (not (= int_res0 #b0000))) (and (RAND from2) (BV_DIFF_REC from2 from1 Times int_res1) (not (= int_res1 #b0000))))) (SET_SUM_REC from1 from2 to Times)))
(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (Time Times) (and (and (RAND from1) (BV_DIFF_REC from1 from2 Times int_res0) (= int_res0 #b0000)) (and (RAND from2) (BV_DIFF_REC from2 from1 Times int_res1) (= int_res1 #b0000)))) (BV_ZERO_REC from1 to Times)))
;; define the array for [ALL_INC]
(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (Time Times) (or (RAND from1) (RAND from2))) (XOR_RUD1_ALL_INC_REC from1 from2 to Times)))

; rule [XOR] [KEY_SENSITIVE] + [KEY_SENSITIVE]
(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (KEY_SENSITIVE from1) (KEY_SENSITIVE from2)) (KEY_SENSITIVE to)))
(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (Time Times) (KEY_SENSITIVE from1) (KEY_SENSITIVE from2)) (BV_ZERO_REC from1 to Times)))
(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (Time Times) (KEY_SENSITIVE from1) (KEY_SENSITIVE from2)) (BVOR_ALL_REC from1 from2 to Times)))

; rule [XOR] [SID] + [SID] ;; TO DO: refinement ;; overlapping with rule [SID]
(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (KEY_IND from1) (KEY_IND from2)) (INTERSECT_LABEL from1 from2)))
(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (KEY_IND from1) (KEY_IND from2) (Time Times) (BV_INTERSECT_REC from1 from2 Times int_res0) (= int_res0 #b0000)) (KEY_IND to)))
(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (KEY_IND from1) (KEY_IND from2) (Time Times) (BV_INTERSECT_REC from1 from2 Times int_res0) (not (= int_res0 #b0000))) (KEY_SENSITIVE to)))
(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (KEY_IND from1) (KEY_IND from2) (Time Times)) (BVOR_ALL_REC from1 from2 to Times)))
(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (KEY_IND from1) (KEY_IND from2) (Time Times)) (BV_ZERO_REC from1 to Times)))

; rule [AO-RUD1] [RAND] + [SID] ;; left operand ;; ;;TYPE
;;;; change (not (KEY_SENSITIVE xxx)) = (or (IND) (RAND));;;;;;
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from1) (KEY_IND from2)) (INTERSECT_LABEL from1 from2)))
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from1) (KEY_IND from2) (Time Times) (BV_INTERSECT_REC from1 from2 Times int_res0) (= int_res0 #b0000)) (KEY_IND to)))
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from1) (KEY_IND from2) (Time Times) (BV_INTERSECT_REC from1 from2 Times int_res0) (not (= int_res0 #b0000))) (KEY_SENSITIVE to)))
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from1) (KEY_IND from2) (Time Times)) (BVOR_ALL_REC from1 from2 to Times)))
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from1) (KEY_IND from2) (Time Times)) (BV_ZERO_REC from1 to Times)))

; rule [AO-RUD1] [RAND] + [KEY_SENSITIVE] ;; TYPE
;; left operand ;; constraint => ALL_INC_left / ALL_INC_right = empty
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (KEY_SENSITIVE from2) (RAND from1)) (KEY_SENSITIVE to)))
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (KEY_SENSITIVE from2) (RAND from1) (Time Times)) (BVOR_ALL_REC from1 from2 to Times)))
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (KEY_SENSITIVE from2) (RAND from1) (Time Times)) (BV_ZERO_REC from1 to Times)))

; rule [AO-RUD2] ;; right operand ;; [RAND] + [KEY_IND] ;; TYPE
;;;; change (not (KEY_SENSITIVE xxx)) = (or (IND) (RAND));;;;;;;
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from2) (KEY_IND from1)) (INTERSECT_LABEL from1 from2)))
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (KEY_IND from1) (RAND from2) (Time Times) (BV_INTERSECT_REC from1 from2 Times int_res0) (= int_res0 #b0000)) (KEY_IND to)))
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (KEY_IND from1) (RAND from2) (Time Times) (BV_INTERSECT_REC from1 from2 Times int_res0) (not (= int_res0 #b0000))) (KEY_SENSITIVE to)))
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (KEY_IND from1) (RAND from2) (Time Times)) (BVOR_ALL_REC from1 from2 to Times)))
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (KEY_IND from1) (RAND from2) (Time Times)) (BV_ZERO_REC from1 to Times)))

;rule [AO-RUD2] ;; right operand ;; [RAND] + [KEY_SENSITIVE]
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from2) (KEY_SENSITIVE from1)) (KEY_SENSITIVE to)))
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from2) (KEY_SENSITIVE from1) (Time Times)) (BVOR_ALL_REC from1 from2 to Times)))
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from2) (KEY_SENSITIVE from1) (Time Times)) (BV_ZERO_REC from1 to Times)))
; rule [AO-RUD3] ;;; TYPE [RAND] + [RAND]
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from1) (RAND from2)) (DIFF_LABEL from1 from2)))
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from1) (RAND from2)) (DIFF_LABEL from2 from1)))
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from1) (RAND from2) (Time Times) (BV_DIFF_REC from1 from2 Times int_res0) (BV_DIFF_REC from2 from1 Times int_res1) (BVOR int_res0 int_res1 int_res2) (not (= int_res2 #b0000))) (KEY_IND to)))
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from1) (RAND from2) (Time Times) (and (and (BV_DIFF_REC from1 from2 Times int_res0) (= int_res0 #b0000)) (and (BV_DIFF_REC from2 from1 Times int_res1) (= int_res1 #b0000)))) (CHECK_SAME from1 from2)))
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (Time Times) (RAND from1) (RAND from2) (BV_SAME_REC from1 from2 Times int_res0) (= int_res0 #b0000)) (KEY_IND to)))
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (Time Times) (RAND from1) (RAND from2) (BV_SAME_REC from1 from2 Times int_res0) (not (= int_res0 #b0000))) (KEY_SENSITIVE to)))
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from1) (RAND from2) (Time Times)) (BVOR_ALL_REC from1 from2 to Times)))
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from1) (RAND from2) (Time Times)) (BV_ZERO_REC from1 to Times)))

; rule [AO] [KEY_SENSITIVE] + [KEY_SENSITIVE] ;; TYPE
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (KEY_SENSITIVE from1) (KEY_SENSITIVE from2)) (KEY_SENSITIVE to)))
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (KEY_SENSITIVE from1) (KEY_SENSITIVE from2) (Time Times)) (BVOR_ALL_REC from1 from2 to Times)))
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (KEY_SENSITIVE from1) (KEY_SENSITIVE from2) (Time Times)) (BV_ZERO_REC from1 to Times)))

; rule [SID] ;; AND OR  ;; TYPE [AO] +  [SID] + [SID]
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (KEY_IND from1) (KEY_IND from2)) (INTERSECT_LABEL from1 from2)))
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (KEY_IND from1) (KEY_IND from2) (Time Times) (BV_INTERSECT_REC from1 from2 Times int_res0) (= int_res0 #b0000)) (KEY_IND to)))
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (KEY_IND from1) (KEY_IND from2) (Time Times) (BV_INTERSECT_REC from1 from2 Times int_res0) (not (= int_res0 #b0000))) (KEY_SENSITIVE to)))
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
;(rule (=> (and (Time Times) (BVAND_ALL_KEY_REC from1 Times int_res0) (= int_res0 #b0000) (BV_IS_EMPTY_REC from1 Times int_bool0) int_bool0) (KEY_IND from1)))

;rule [assign] + [KET_SENSITIVE]
(rule (=> (and (assign to from) (KEY_SENSITIVE from)) (KEY_SENSITIVE to)))
;rule [assign] + [KEY_IND]
(rule (=> (and (assign to from) (KEY_IND from)) (KEY_IND to)))
;rule [assign] + [RAND]
(rule (=> (and (assign to from) (RAND from)) (RAND to)))
;rule [assign] array
(rule (=> (and (assign to from) (Time Times)) (BV_EQUAL_ALL_REC from to Times)))
(rule (=> (and (assign to from) (Time Times)) (BV_EQUAL_RAND_REC from to Times)))

; rule [binary_constant] + [KEY_SENSITIVE]
(rule (=> (and (binary_constant to from1) (KEY_SENSITIVE from1)) (KEY_SENSITIVE to)))
; rule [binary_constant] + [KEY_IND]
(rule (=> (and (binary_constant to from1) (KEY_IND from1)) (KEY_IND to)))
; rule [binary_constant] + [RAND]
(rule (=> (and (binary_constant to from1) (RAND from1)) (RAND to)))
; rule [binary_constant] array
(rule (=> (and (binary_constant to from1) (Time Times)) (BV_EQUAL_ALL_REC from1 to Times)))
(rule (=> (and (binary_constant to from1) (Time Times)) (BV_EQUAL_RAND_REC from1 to Times)))

; rule <zext>, <imcp> and <trunc> can be regarded as the load assignment
(rule (=> (zext_assign to from1) (assign to from1)))
(rule (=> (trunc_assign to from1) (assign to from1)))
(rule (=> (icmp_assign to from1) (assign to from1)))

;load_assign, store_assign ===> assign
(rule (=> (load_assign to from1) (assign to from1)))
(rule (=> (store_assign to from1) (assign to from1)))
(rule (=> (and (assign to from1) (assign from1 from2)) (assign to from2)))

; equal_assign: more general assign, only targeting at equal relation
(rule (=> (assign to from1) (equal_assign to from1)))
(rule (=> (binary_constant to from1) (equal_assign to from1)))
(rule (=> true (equal_assign from1 from1)))
(rule (=> (equal_assign from1 from2) (equal_assign from2 from1)))
(rule (=> (and (equal_assign from1 from2) (equal_assign from2 to)) (equal_assign from1 to)))

; for rule share ;; and the transition inside load and store
(rule (=> (share from1 from2) (share from2 from1)))
(rule (=> (and (share from from1) (share from1 from2)) (share from from2)))

;; for rule share symmetric
(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (share to from1) (KEY_SENSITIVE from2)) (HD_SENSITIVE to from1)))
(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (share to from2) (KEY_SENSITIVE from1)) (HD_SENSITIVE to from2)))
;; define the case for HD sensitive (indirect)
(rule (=> (and (share to from) (equal_assign from_e from) (equal_assign to_e to) (xor_assign_left to_e from_e) (xor_assign_right to_e from1) (KEY_SENSITIVE from1)) (HD_SENSITIVE to from)))
(rule (=> (and (share to from) (equal_assign from_e from) (equal_assign to_e to) (xor_assign_left to_e from1) (xor_assign_right to_e from_e) (KEY_SENSITIVE from1)) (HD_SENSITIVE to from)))

;;classify two different HD_sensitive types
(rule (=> (and (load_assign from1 from) (store_assign to from1) (HD_SENSITIVE to from2)) (HD_SENSITIVE_2 to from2)))
(rule (=> (and (load_assign from1 from) (store_assign to from1) (HD_SENSITIVE from2 to)) (HD_SENSITIVE_2 from2 to)))

(rule (Time #b1))
(rule (RAND_NUMBER #b1 #b0011))
(rule (KEY_NUMBER #b1 #b0100))
;share_register_variable_pair: %rx.addr %X
(rule (share #x0003 #x000b))
;share_register_variable_pair: %X %T1
(rule (share #x000b #x0004))
;share_register_variable_pair: %T1 %T2
(rule (share #x0004 #x0005))
;share_register_variable_pair: %T2 %T3
(rule (share #x0005 #x0006))
;share_register_variable_pair: %R.addr %R2
(rule (share #x0001 #x0007))
;share_register_variable_pair: %R2 %A1
(rule (share #x0007 #x0008))
;share_register_variable_pair: %A1 %A2
(rule (share #x0008 #x0009))
;share_register_variable_pair: %A2 %A3
(rule (share #x0009 #x000a))
; user specify the sensitive variable
;### Begin facts 
;   %R.addr = alloca i32, align 4
;(alloca #x0001 R.addr )
;   %x.addr = alloca i32, align 4
;(alloca #x0002 x.addr )
;   %rx.addr = alloca i32, align 4
;(alloca #x0003 rx.addr )
;   %T1 = alloca i32, align 4
;(alloca #x0004 T1 )
;   %T2 = alloca i32, align 4
;(alloca #x0005 T2 )
;   %T3 = alloca i32, align 4
;(alloca #x0006 T3 )
;   %R2 = alloca i32, align 4
;(alloca #x0007 R2 )
;   %A1 = alloca i32, align 4
;(alloca #x0008 A1 )
;   %A2 = alloca i32, align 4
;(alloca #x0009 A2 )
;   %A3 = alloca i32, align 4
;(alloca #x000a A3 )
;   %X = alloca i32, align 4
;(alloca #x000b X )
;   store i32 %R, i32* %R.addr, align 4
;R==> type
(rule (RAND #x0001))
(rule (REC_RAND_VAR #x0001 #b1 #b0001))
(rule (REC_ALL_INC #x0001 #b1 #b0001))

;   store i32 %x, i32* %x.addr, align 4
;x==> type
(rule (KEY_SENSITIVE #x0002))
(rule (REC_RAND_VAR #x0002 #b1 #b0000 ))
(rule (REC_ALL_INC #x0002 #b1 #b0100 ))

;   store i32 %rx, i32* %rx.addr, align 4
;rx==> type
(rule (RAND #x0003))
(rule (REC_RAND_VAR #x0003 #b1 #b0010))
(rule (REC_ALL_INC #x0003 #b1 #b0010))

;   %0 = load i32* %x.addr, align 4
(rule (load_assign #x000f #x0002))
;   %1 = load i32* %rx.addr, align 4
(rule (load_assign #x0010 #x0003))
;   %xor = xor i32 %0, %1
(rule (xor_assign_left #x0011 #x000f))
;   %xor = xor i32 %0, %1
(rule (xor_assign_right #x0011 #x0010))
;   store i32 %xor, i32* %X, align 4
(rule (store_assign #x000b #x0011))
;   %2 = load i32* %X, align 4
(rule (load_assign #x0013 #x000b))
;   %3 = load i32* %R.addr, align 4
(rule (load_assign #x0014 #x0001))
;   %xor1 = xor i32 %2, %3
(rule (xor_assign_left #x0015 #x0013))
;   %xor1 = xor i32 %2, %3
(rule (xor_assign_right #x0015 #x0014))
;   store i32 %xor1, i32* %T1, align 4
(rule (store_assign #x0004 #x0015))
;   %4 = load i32* %T1, align 4
(rule (load_assign #x0017 #x0004))
;   %5 = load i32* %R.addr, align 4
(rule (load_assign #x0018 #x0001))
;   %xor2 = xor i32 %4, %5
(rule (xor_assign_left #x0019 #x0017))
;   %xor2 = xor i32 %4, %5
(rule (xor_assign_right #x0019 #x0018))
;   store i32 %xor2, i32* %T2, align 4
(rule (store_assign #x0005 #x0019))
;   %6 = load i32* %T2, align 4
(rule (load_assign #x001b #x0005))
;   %7 = load i32* %X, align 4
(rule (load_assign #x001c #x000b))
;   %xor3 = xor i32 %6, %7
(rule (xor_assign_left #x001d #x001b))
;   %xor3 = xor i32 %6, %7
(rule (xor_assign_right #x001d #x001c))
;   store i32 %xor3, i32* %T3, align 4
(rule (store_assign #x0006 #x001d))
;   %8 = load i32* %R.addr, align 4
(rule (load_assign #x001f #x0001))
;   %9 = load i32* %rx.addr, align 4
(rule (load_assign #x0020 #x0003))
;   %xor4 = xor i32 %8, %9
(rule (xor_assign_left #x0021 #x001f))
;   %xor4 = xor i32 %8, %9
(rule (xor_assign_right #x0021 #x0020))
;   store i32 %xor4, i32* %R2, align 4
(rule (store_assign #x0007 #x0021))
;   %10 = load i32* %X, align 4
(rule (load_assign #x0023 #x000b))
;   %11 = load i32* %R2, align 4
(rule (load_assign #x0024 #x0007))
;   %xor5 = xor i32 %10, %11
(rule (xor_assign_left #x0025 #x0023))
;   %xor5 = xor i32 %10, %11
(rule (xor_assign_right #x0025 #x0024))
;   store i32 %xor5, i32* %A1, align 4
(rule (store_assign #x0008 #x0025))
;   %12 = load i32* %A1, align 4
(rule (load_assign #x0027 #x0008))
;   %13 = load i32* %R2, align 4
(rule (load_assign #x0028 #x0007))
;   %xor6 = xor i32 %12, %13
(rule (xor_assign_left #x0029 #x0027))
;   %xor6 = xor i32 %12, %13
(rule (xor_assign_right #x0029 #x0028))
;   store i32 %xor6, i32* %A2, align 4
(rule (store_assign #x0009 #x0029))
;   %14 = load i32* %A2, align 4
(rule (load_assign #x002b #x0009))
;   %15 = load i32* %T3, align 4
(rule (load_assign #x002c #x0006))
;   %xor7 = xor i32 %14, %15
(rule (xor_assign_left #x002d #x002b))
;   %xor7 = xor i32 %14, %15
(rule (xor_assign_right #x002d #x002c))
;   store i32 %xor7, i32* %A3, align 4
(rule (store_assign #x000a #x002d))
;   %16 = load i32* %A3, align 4
(rule (load_assign #x002f #x000a))
;query KEY_IND type
(query KEY_IND :print-answer true)
;query KEY_SENSITIVE type
(query KEY_SENSITIVE :print-answer true)
;query RAND type
(query RAND :print-answer true)
;query under HD model, key_sensitive
(query HD_SENSITIVE :print-answer true)
(query HD_SENSITIVE_2 :print-answer true)

;###### End Facts
