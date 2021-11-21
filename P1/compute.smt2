(set-option :fixedpoint.engine datalog)
; this sort is used to define all the relations
(define-sort s () (_ BitVec 8))

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

; rule [AO-RUD1] [RAND] + [NO_KEY] ;; left operand ;; ;;TYPE
;;;; change (not (KEY_SENSITIVE xxx)) = (or (IND) (RAND));;;;;;
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from1) (or (KEY_IND from2) (RAND from2))) (INTERSECT_LABEL from1 from2)))
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from1) (or (KEY_IND from2) (RAND from2)) (Time Times) (BV_INTERSECT_REC from1 from2 Times int_res0) (= int_res0 #b0000)) (KEY_IND to)))
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from1) (or (KEY_IND from2) (RAND from2)) (Time Times) (BV_INTERSECT_REC from1 from2 Times int_res0) (not (= int_res0 #b0000))) (KEY_SENSITIVE to)))
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from1) (or (KEY_IND from2) (RAND from2)) (Time Times)) (BVOR_ALL_REC from1 from2 to Times)))
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from1) (or (KEY_IND from2) (RAND from2)) (Time Times)) (BV_ZERO_REC from1 to Times)))

; rule [AO-RUD1] [RAND] + [KEY_SENSITIVE] ;; TYPE
;; left operand ;; constraint => ALL_INC_left / ALL_INC_right = empty
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (KEY_SENSITIVE from2) (RAND from1)) (KEY_SENSITIVE to)))
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (KEY_SENSITIVE from2) (RAND from1) (Time Times)) (BVOR_ALL_REC from1 from2 to Times)))
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (KEY_SENSITIVE from2) (RAND from1) (Time Times)) (BV_ZERO_REC from1 to Times)))

; rule [AO-RUD2] ;; right operand ;; [RAND] + [NO KEY] ;; TYPE
;;;; change (not (KEY_SENSITIVE xxx)) = (or (IND) (RAND));;;;;;;
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from2) (or (KEY_IND from1) (RAND from1))) (INTERSECT_LABEL from1 from2)))
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (or (KEY_IND from1) (RAND from1)) (RAND from2) (Time Times) (BV_INTERSECT_REC from1 from2 Times int_res0) (= int_res0 #b0000)) (KEY_IND to)))
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (or (KEY_IND from1) (RAND from1)) (RAND from2) (Time Times) (BV_INTERSECT_REC from1 from2 Times int_res0) (not (= int_res0 #b0000))) (KEY_IND to)))
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (or (KEY_IND from1) (RAND from1)) (RAND from2) (Time Times)) (BVOR_ALL_REC from1 from2 to Times)))
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (or (KEY_IND from1) (RAND from1)) (RAND from2) (Time Times)) (BV_ZERO_REC from1 to Times)))

;rule [AO-RUD2] ;; right operand ;; [RAND] + [KEY_SENSITIVE]
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from2) (KEY_SENSITIVE from1)) (KEY_SENSITIVE to)))
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from2) (KEY_SENSITIVE from1) (Time Times)) (BVOR_ALL_REC from1 from2 to Times)))
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from2) (KEY_SENSITIVE from1) (Time Times)) (BV_ZERO_REC from1 to Times)))
; rule [AO-RUD3] ;;; TYPE
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from1) (RAND from2)) (DIFF_LABEL from1 from2)))
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from1) (RAND from2) (Time Times) (BV_DIFF_REC from1 from2 Times int_res0) (BV_DIFF_REC from2 from1 Times int_res1) (BVOR int_res0 int_res1 int_res2) (not (= int_res2 #b0000))) (KEY_IND to)))
(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from1) (RAND from2) (Time Times) (BV_DIFF_REC from1 from2 Times int_res0) (BV_DIFF_REC from2 from1 Times int_res1) (BVOR int_res0 int_res1 int_res2) (= int_res2 #b0000)) (KEY_SENSITIVE to)))
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

; rule [equal_assign]
(rule (=> (and (equal_assign to from1) (RAND from1)) (RAND to)))
(rule (=> (and (equal_assign to from1) (KEY_IND from1)) (KEY_IND to)))
(rule (=> (and (equal_assign to from1) (KEY_SENSITIVE from1)) (KEY_SENSITIVE to)))

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
(rule (=> (zext_assign to from1) (load_assign to from1)))
(rule (=> (trunc_assign to from1) (load_assign to from1)))
(rule (=> (icmp_assign to from1) (load_assign to from1)))

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
;(rule (=> (and (load_assign to from1) (share from1 from2)) (share to from2)))
;(rule (=> (and (load_assign to from1) (share to from2)) (share from1 from2)))
;(rule (=> (and (store_assign to from1) (share from1 from2)) (share to from2)))
;(rule (=> (and (store_assign to from1) (share to from2)) (share from1 from2)))
;; for rule share symmetric
(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (share to from1) (KEY_SENSITIVE from2)) (HD_SENSITIVE to from1)))
(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (share to from2) (KEY_SENSITIVE from1)) (HD_SENSITIVE to from2)))
;; define the case for HD sensitive (indirect)
(rule (=> (and (share to from) (equal_assign from_e from) (equal_assign to_e to) (xor_assign_left to_e from_e) (xor_assign_right to_e from1) (KEY_SENSITIVE from1)) (HD_SENSITIVE to from)))
(rule (=> (and (share to from) (equal_assign from_e from) (equal_assign to_e to) (xor_assign_left to_e from1) (xor_assign_right to_e from_e) (KEY_SENSITIVE from1)) (HD_SENSITIVE to from)))

(rule (Time #b1))
(rule (RAND_NUMBER #b1 #b0011))
(rule (KEY_NUMBER #b1 #b1100))
;share_register_variable_pair: %st10_orig.addr %st10
(rule (share #x04 #x09))
;share_register_variable_pair: %st10 %st2_orig.addr
(rule (share #x09 #x03))
;share_register_variable_pair: %st2_orig.addr %st2
(rule (share #x03 #x07))
;share_register_variable_pair: %st2 %r24
(rule (share #x07 #x06))
;share_register_variable_pair: %r24 %st10
(rule (share #x06 #x09))
;share_register_variable_pair: %st10 %r25
(rule (share #x09 #x05))
;share_register_variable_pair: %r25 %sTT2
(rule (share #x05 #x08))
;share_register_variable_pair: %sTT2 %r24
(rule (share #x08 #x06))
;share_register_variable_pair: %r24 %sTT10
(rule (share #x06 #x0a))
;share_register_variable_pair: %st10_orig.addr %sTT2
(rule (share #x04 #x08))


; user specify the sensitive variable
;### Begin facts 
;   %r1.addr = alloca i8, align 1
;(alloca #x01 r1.addr )
;   %r2.addr = alloca i8, align 1
;(alloca #x02 r2.addr )
;   %st2_orig.addr = alloca i8, align 1
;(alloca #x03 st2_orig.addr )
;   %st10_orig.addr = alloca i8, align 1
;(alloca #x04 st10_orig.addr )
;   %r25 = alloca i8, align 1
;(alloca #x05 r25 )
;   %r24 = alloca i8, align 1
;(alloca #x06 r24 )
;   %st2 = alloca i8, align 1
;(alloca #x07 st2 )
;   %sTT2 = alloca i8, align 1
;(alloca #x08 sTT2 )
;   %st10 = alloca i8, align 1
;(alloca #x09 st10 )
;   %sTT10 = alloca i8, align 1
;(alloca #x0a sTT10 )
;   %frombool = zext i1 %r1 to i8
;r1==> type
(rule (RAND #b00001011))
(rule (REC_RAND_VAR #b00001011 #b1 #b0001))
(rule (REC_ALL_INC #b00001011 #b1 #b0001))

;   store i8 %frombool, i8* %r1.addr, align 1
(rule (store_assign #b00000001 #b00001011))
;   %frombool1 = zext i1 %r2 to i8
;r2==> type
(rule (RAND #b00001101))
(rule (REC_RAND_VAR #b00001101 #b1 #b0010))
(rule (REC_ALL_INC #b00001101 #b1 #b0010))

;   store i8 %frombool1, i8* %r2.addr, align 1
(rule (store_assign #b00000010 #b00001101))
;   %frombool2 = zext i1 %st2_orig to i8
;st2_orig==> type
(rule (KEY_SENSITIVE #b00001111))
(rule (REC_RAND_VAR #b00001111 #b1 #b0000 ))
(rule (REC_ALL_INC #b00001111 #b1 #b0100 ))

;   store i8 %frombool2, i8* %st2_orig.addr, align 1
(rule (store_assign #b00000011 #b00001111))
;   %frombool3 = zext i1 %st10_orig to i8
;st10_orig==> type
(rule (KEY_SENSITIVE #b00010001))
(rule (REC_RAND_VAR #b00010001 #b1 #b0000 ))
(rule (REC_ALL_INC #b00010001 #b1 #b1000 ))

;   store i8 %frombool3, i8* %st10_orig.addr, align 1
(rule (store_assign #b00000100 #b00010001))
;   %0 = load i8* %st10_orig.addr, align 1
(rule (load_assign #b00010011 #b00000100))
;   %tobool = trunc i8 %0 to i1
(rule (trunc_assign #b00010100 #b00010011))
;   %conv = zext i1 %tobool to i32
(rule (zext_assign #b00010101 #b00010100))
;   %1 = load i8* %r1.addr, align 1
(rule (load_assign #b00010110 #b00000001))
;   %tobool4 = trunc i8 %1 to i1
(rule (trunc_assign #b00010111 #b00010110))
;   %conv5 = zext i1 %tobool4 to i32
(rule (zext_assign #b00011000 #b00010111))
;   %xor = xor i32 %conv, %conv5
(rule (xor_assign_left #b00011001 #b00010101))
;   %xor = xor i32 %conv, %conv5
(rule (xor_assign_right #b00011001 #b00011000))
;   %tobool6 = icmp ne i32 %xor, 0
(rule (icmp_assign #b00011010 #b00011001))
;   %frombool7 = zext i1 %tobool6 to i8
(rule (zext_assign #b00011011 #b00011010))
;   store i8 %frombool7, i8* %st10, align 1
(rule (store_assign #b00001001 #b00011011))
;   %2 = load i8* %st2_orig.addr, align 1
(rule (load_assign #b00011101 #b00000011))
;   %tobool8 = trunc i8 %2 to i1
(rule (trunc_assign #b00011110 #b00011101))
;   %conv9 = zext i1 %tobool8 to i32
(rule (zext_assign #b00011111 #b00011110))
;   %3 = load i8* %r1.addr, align 1
(rule (load_assign #b00100000 #b00000001))
;   %tobool10 = trunc i8 %3 to i1
(rule (trunc_assign #b00100001 #b00100000))
;   %conv11 = zext i1 %tobool10 to i32
(rule (zext_assign #b00100010 #b00100001))
;   %xor12 = xor i32 %conv9, %conv11
(rule (xor_assign_left #b00100011 #b00011111))
;   %xor12 = xor i32 %conv9, %conv11
(rule (xor_assign_right #b00100011 #b00100010))
;   %tobool13 = icmp ne i32 %xor12, 0
(rule (icmp_assign #b00100100 #b00100011))
;   %frombool14 = zext i1 %tobool13 to i8
(rule (zext_assign #b00100101 #b00100100))
;   store i8 %frombool14, i8* %st2, align 1
(rule (store_assign #b00000111 #b00100101))
;   %4 = load i8* %st2, align 1
(rule (load_assign #b00100111 #b00000111))
;   %tobool15 = trunc i8 %4 to i1
(rule (trunc_assign #b00101000 #b00100111))
;   %conv16 = zext i1 %tobool15 to i32
(rule (zext_assign #b00101001 #b00101000))
;   %xor17 = xor i32 %conv16, 0
(rule (binary_constant #b00101010 #b00101001))
;   %tobool18 = icmp ne i32 %xor17, 0
(rule (icmp_assign #b00101011 #b00101010))
;   %frombool19 = zext i1 %tobool18 to i8
(rule (zext_assign #b00101100 #b00101011))
;   store i8 %frombool19, i8* %r24, align 1
(rule (store_assign #b00000110 #b00101100))
;   %5 = load i8* %st10, align 1
(rule (load_assign #b00101110 #b00001001))
;   %tobool20 = trunc i8 %5 to i1
(rule (trunc_assign #b00101111 #b00101110))
;   %conv21 = zext i1 %tobool20 to i32
(rule (zext_assign #b00110000 #b00101111))
;   %xor22 = xor i32 %conv21, 0
(rule (binary_constant #b00110001 #b00110000))
;   %tobool23 = icmp ne i32 %xor22, 0
(rule (icmp_assign #b00110010 #b00110001))
;   %frombool24 = zext i1 %tobool23 to i8
(rule (zext_assign #b00110011 #b00110010))
;   store i8 %frombool24, i8* %r25, align 1
(rule (store_assign #b00000101 #b00110011))
;   %6 = load i8* %r25, align 1
(rule (load_assign #b00110101 #b00000101))
;   %tobool25 = trunc i8 %6 to i1
(rule (trunc_assign #b00110110 #b00110101))
;   %conv26 = zext i1 %tobool25 to i32
(rule (zext_assign #b00110111 #b00110110))
;   %xor27 = xor i32 %conv26, 0
(rule (binary_constant #b00111000 #b00110111))
;   %tobool28 = icmp ne i32 %xor27, 0
(rule (icmp_assign #b00111001 #b00111000))
;   %frombool29 = zext i1 %tobool28 to i8
(rule (zext_assign #b00111010 #b00111001))
;   store i8 %frombool29, i8* %sTT2, align 1
(rule (store_assign #b00001000 #b00111010))
;   %7 = load i8* %r24, align 1
(rule (load_assign #b00111100 #b00000110))
;   %tobool30 = trunc i8 %7 to i1
(rule (trunc_assign #b00111101 #b00111100))
;   %conv31 = zext i1 %tobool30 to i32
(rule (zext_assign #b00111110 #b00111101))
;   %xor32 = xor i32 %conv31, 0
(rule (binary_constant #b00111111 #b00111110))
;   %tobool33 = icmp ne i32 %xor32, 0
(rule (icmp_assign #b01000000 #b00111111))
;   %frombool34 = zext i1 %tobool33 to i8
(rule (zext_assign #b01000001 #b01000000))
;   store i8 %frombool34, i8* %sTT10, align 1
(rule (store_assign #b00001010 #b01000001))
;   %8 = load i8* %sTT2, align 1
(rule (load_assign #b01000011 #b00001000))
;   %tobool35 = trunc i8 %8 to i1
(rule (trunc_assign #b01000100 #b01000011))
;   %conv36 = zext i1 %tobool35 to i32
(rule (zext_assign #b01000101 #b01000100))
;   %9 = load i8* %sTT10, align 1
(rule (load_assign #b01000110 #b00001010))
;   %tobool37 = trunc i8 %9 to i1
(rule (trunc_assign #b01000111 #b01000110))
;   %conv38 = zext i1 %tobool37 to i32
(rule (zext_assign #b01001000 #b01000111))
;   %sub = sub nsw i32 %conv36, %conv38
(rule (assign #b01001001 #b01000101))
;   %sub = sub nsw i32 %conv36, %conv38
(rule (assign #b01001001 #b01001000))
;   %tobool39 = icmp ne i32 %sub, 0
(rule (icmp_assign #b01001010 #b01001001))
;query KEY_IND type
(query KEY_IND :print-answer true)
;query KEY_SENSITIVE type
(query KEY_SENSITIVE :print-answer true)
;query RAND type
(query RAND :print-answer true)
;query under HD model, key_sensitive
;(query HD_SENSITIVE :print-answer true)
; trach the relation between intermediate var and the input parameters
(declare-rel q1(s))
(rule (=> (and (HD_SENSITIVE from1 from2) (assign to from1)) (q1 to)))
(query q1 :print-answer true)

;###### End Facts
