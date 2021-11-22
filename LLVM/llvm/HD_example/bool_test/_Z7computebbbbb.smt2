(set-option :fixedpoint.engine datalog)
; this sort is used to define all the relations
(define-sort s () (_ BitVec 16))

(define-sort BitSet () (_ BitVec 4))
(define-sort ind () (_ BitVec 3))
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

; declare the types which are gonna be used
(declare-rel KEY_SENSITIVE (s))
(declare-rel KEY_IND (s))
(declare-rel CONSTANT (s))
(declare-rel RAND (s))

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
(rule (=> (and (BVAND_REC var_x var_y var_z Times) (not (= Times #b000)) (= Times_New (bvsub Times #b001))) (BVAND_REC var_x var_y var_z Times_New)))
;; BV [AND] = [KEY] && [ALL_INC] ;;; for the [NO KEY] rule ;;;;;;
;(rule (=> (and (REC_ALL_INC var_x Times X) (KEY_NUMBER Times KEY_NUM) (BVAND X KEY_NUM int_res0) (= Times #b001)) (BVAND_ALL_KEY_REC var_x Times int_res0)))
;(rule (=> (and (BVAND_ALL_KEY_REC var_x Times_New int_res0) (REC_ALL_INC var_x Times X) (KEY_NUMBER Times KEY_NUM) (BVAND X KEY_NUM int_res1) (= Times_New (bvsub Times #b001)) (not (= Times #b001)) (BVOR int_res0 int_res1 int_res2)) (BVAND_ALL_KEY_REC var_x Times int_res2)))
;; BV [OR] [RAND_VAR]
(rule (=> (and (REC_RAND_VAR var_x Times X) (REC_RAND_VAR var_y Times Y) (BVOR_RAND_REC var_x var_y var_z Times) (BVOR X Y XY)) (REC_RAND_VAR var_z Times XY)))
(rule (=> (and (BVOR_RAND_REC var_x var_y var_z Times) (not (= Times #b000)) (= Times_New (bvsub Times #b001))) (BVOR_RAND_REC var_x var_y var_z Times_New)))
;; BV [OR] [ALL_INC]
(rule (=> (and (REC_ALL_INC var_x Times X) (REC_ALL_INC var_y Times Y) (BVOR_ALL_REC var_x var_y var_z Times) (BVOR X Y XY)) (REC_ALL_INC var_z Times XY)))
(rule (=> (and (BVOR_ALL_REC var_x var_y var_z Times) (not (= Times #b000)) (= Times_New (bvsub Times #b001))) (BVOR_ALL_REC var_x var_y var_z Times_New)))
;; BV [Intersect] [ALL_INC]
(rule (=> (and (REC_ALL_INC var_x Times X) (REC_ALL_INC var_y Times Y) (= Times #b001) (BV_Intersect X Y XY)(INTERSECT_LABEL var_x var_y)) (BV_INTERSECT_REC var_x var_y Times XY)))
(rule (=> (and (REC_RAND_VAR var_x Times X) (REC_ALL_INC var_y Times Y) (not (= Times #b001)) (BV_Intersect X Y XY) (INTERSECT_LABEL var_x var_y) (= Times_New (bvsub Times #b001)) (BV_INTERSECT_REC var_x var_y Times_New XY_past) (BVOR XY XY_past int_res0)) (BV_INTERSECT_REC var_x var_y Times int_res0)))
;; BV [DIFF] [RAND_VAR][ALL_INC]
(rule (=> (and (REC_RAND_VAR var_x Times X) (REC_ALL_INC var_y Times Y) (= Times #b001) (BV_Diff X Y XY) (DIFF_LABEL var_x var_y)) (BV_DIFF_REC var_x var_y Times XY)))
(rule (=> (and (REC_RAND_VAR var_x Times X) (REC_ALL_INC var_y Times Y) (not (= Times #b001)) (BV_Diff X Y XY) (DIFF_LABEL var_x var_y) (= Times_New (bvsub Times #b001)) (BV_DIFF_REC var_x var_y Times_New XY_past) (BVOR XY XY_past int_res0)) (BV_DIFF_REC var_x var_y Times int_res0)))
;; BV [SET_SUM] [RAND_VAR] [RAND_VAR]
(rule (=> (and (REC_RAND_VAR var_x Times X) (REC_RAND_VAR var_y Times Y) (SET_SUM_REC var_x var_y var_z Times) (SET_SUM X Y XY)) (REC_RAND_VAR var_z Times XY)))
(rule (=> (and (SET_SUM_REC var_x var_y var_z Times) (not (= Times_New #b000)) (= Times_New (bvsub Times #b001))) (SET_SUM_REC var_x var_y var_z Times_New)))
;; BV [XOR_RUD1_ALL_INC_REC] => generate the ALL_INC
(rule (=> (and (REC_RAND_VAR var_x Times X_R) (REC_RAND_VAR var_y Times Y_R) (REC_ALL_INC var_x Times X_A) (REC_ALL_INC var_y Times Y_A) (RAND_NUMBER Times RAND_NUM) (XOR_RUD1_ALL_INC X_A Y_A X_R Y_R RAND_NUM XY) (XOR_RUD1_ALL_INC_REC var_x var_y var_z Times)) (REC_ALL_INC var_z Times XY)))
(rule (=> (and (XOR_RUD1_ALL_INC_REC var_x var_y var_z Times) (= Times_New (bvsub Times #b001)) (not (= Times_New #b000))) (XOR_RUD1_ALL_INC_REC var_x var_y var_z Times_New)))
;; BV [BV_EQUAL] ;; generate the same bit vector [RAND_VAR] => [RAND_VAR]
(rule (=> (and (REC_RAND_VAR var_x Times X) (BV_EQUAL_RAND_REC var_x var_y Times)) (REC_RAND_VAR var_y Times X)))
(rule (=> (and (BV_EQUAL_RAND_REC var_x var_y Times) (= Times_New (bvsub Times #b001)) (not (= Times_New #b000))) (BV_EQUAL_RAND_REC var_x var_y Times_New)))
;; BV [BV_EQUAL] ;; [ALL_INC] => [ALL_INC]
(rule (=> (and (REC_ALL_INC var_x Times X) (BV_EQUAL_ALL_REC var_x var_y Times)) (REC_ALL_INC var_y Times X)))
(rule (=> (and (BV_EQUAL_ALL_REC var_x var_y Times) (= Times_New (bvsub Times #b001)) (not (= Times_New #b000))) (BV_EQUAL_ALL_REC var_x var_y Times_New)))
;; BV [BV_ZERO] ;; [RAND]
(rule (=> (and (REC_RAND_VAR var_x Times X) (BV_ZERO_REC var_x var_y Times) (= XY #b0000)) (REC_RAND_VAR var_y Times XY)))
(rule (=> (and (BV_ZERO_REC var_x var_y Times) (= Times_New (bvsub Times #b001)) (not (= Times_New #b000))) (BV_ZERO_REC var_x var_y Times_New)))
;; BV [IS EMPTY] [RAND_VAR] ;;;; for the [NO KEY] rule
;(rule (=> (and (REC_RAND_VAR var_x Times X) (= Times #b001) (ISEMPTY X int_bool0)) (BV_IS_EMPTY_REC var_x Times int_bool0)))
;(rule (=> (and (REC_RAND_VAR var_x Times X) (ISEMPTY X int_bool0) (not (= Times #b001)) (= Times_New (bvsub Times #b001)) (BV_IS_EMPTY_REC var_x Times_New int_bool1)) (BV_IS_EMPTY_REC var_x Times (and int_bool0 int_bool1))))

; [RULE] define the assign relation
(rule (=> (assign to from) (TDEP to from)))
(rule (=> (xor_assign_left to from) (assign to from)))
(rule (=> (xor_assign_right to from) (assign to from)))
(rule (=> (andor_assign_left to from) (assign to from)))
(rule (=> (andor_assign_right to from) (assign to from)))
(rule (=> (not_assign to from) (assign to from)))
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
(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (Time Times) (and (and (RAND from1) (BV_DIFF_REC from1 from2 Times int_res0) (= int_res0 #b0000)) (and (RAND from2) (BV_DIFF_REC from2 from1 Times int_res1) (= int_res1 #b0000)))) (KEY_SENSITIVE to)))
(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (Time Times) (or (and (RAND from1) (BV_DIFF_REC from1 from2 Times int_res0) (not (= int_res0 #b0000))) (and (RAND from2) (BV_DIFF_REC from2 from1 Times int_res1) (not (= int_res1 #b0000))))) (SET_SUM_REC from1 from2 to Times)))
(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (Time Times) (and (and (RAND from1) (BV_DIFF_REC from1 from2 Times int_res0) (= int_res0 #b0000)) (and (RAND from2) (BV_DIFF_REC from2 from1 Times int_res1) (= int_res1 #b0000)))) (BV_ZERO_REC from1 to Times)))
; rule: [XOR_RUD1]
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

(rule (Time #b100))
(rule (RAND_NUMBER #b000 #b0011))
(rule (KEY_NUMBER #b000 #b1100))
(rule (RAND_NUMBER #b001 #b0000))
(rule (KEY_NUMBER #b001 #b0000))
(rule (RAND_NUMBER #b010 #b0000))
(rule (KEY_NUMBER #b010 #b0000))


; user specify the sensitive variable
;### Begin facts 
;   %frombool = zext i1 %r1 to i8
;r1==> type
(rule (RAND #b0000000000001010))
(rule (REC_RAND_VAR #b0000000000001010 #b000 #b0001))
(rule (REC_ALL_INC #b0000000000001010 #b000 #b0001))
(rule (REC_RAND_VAR #b0000000000001010 #b001 #b0000))
(rule (REC_ALL_INC #b0000000000001010 #b001 #b0000))
(rule (REC_RAND_VAR #b0000000000001010 #b010 #b0000))
(rule (REC_ALL_INC #b0000000000001010 #b010 #b0000))

;   store i8 %frombool, i8* %r1.addr, align 1
(rule (store_assign #b0000000000001010 #b0000000000000001))
;   %frombool1 = zext i1 %r2 to i8
;r2==> type
(rule (RAND #b0000000000001100))
(rule (REC_RAND_VAR #b0000000000001100 #b000 #b0010))
(rule (REC_ALL_INC #b0000000000001100 #b000 #b0010))
(rule (REC_RAND_VAR #b0000000000001100 #b001 #b0000))
(rule (REC_ALL_INC #b0000000000001100 #b001 #b0000))
(rule (REC_RAND_VAR #b0000000000001100 #b010 #b0000))
(rule (REC_ALL_INC #b0000000000001100 #b010 #b0000))

;   store i8 %frombool1, i8* %r2.addr, align 1
(rule (store_assign #b0000000000001100 #b0000000000000010))
;   %frombool2 = zext i1 %k1 to i8
;k1==> type
(rule (KEY_SENSITIVE #b0000000000001110))
(rule (REC_RAND_VAR #b0000000000001110 #b000 #b0000 ))
(rule (REC_ALL_INC #b0000000000001110 #b000 #b0100 ))
(rule (REC_RAND_VAR #b0000000000001110 #b001 #b0000 ))
(rule (REC_ALL_INC #b0000000000001110 #b001 #b0000 ))
(rule (REC_RAND_VAR #b0000000000001110 #b010 #b0000 ))
(rule (REC_ALL_INC #b0000000000001110 #b010 #b0000 ))

;   store i8 %frombool2, i8* %k1.addr, align 1
(rule (store_assign #b0000000000001110 #b0000000000000011))
;   %frombool3 = zext i1 %k2 to i8
;k2==> type
(rule (KEY_SENSITIVE #b0000000000010000))
(rule (REC_RAND_VAR #b0000000000010000 #b000 #b0000 ))
(rule (REC_ALL_INC #b0000000000010000 #b000 #b0100 ))
(rule (REC_RAND_VAR #b0000000000010000 #b001 #b0000 ))
(rule (REC_ALL_INC #b0000000000010000 #b001 #b0000 ))
(rule (REC_RAND_VAR #b0000000000010000 #b010 #b0000 ))
(rule (REC_ALL_INC #b0000000000010000 #b010 #b0000 ))

;   store i8 %frombool3, i8* %k2.addr, align 1
(rule (store_assign #b0000000000010000 #b0000000000000100))
;   %frombool4 = zext i1 %p1 to i8
;p1==> type
(rule (CONSTANT #b0000000000010010))
(rule (REC_RAND_VAR #b0000000000010010 #b000 #b0000 ))
(rule (REC_ALL_INC #b0000000000010010 #b000 #b0100 ))
(rule (REC_RAND_VAR #b0000000000010010 #b001 #b0000 ))
(rule (REC_ALL_INC #b0000000000010010 #b001 #b0000 ))
(rule (REC_RAND_VAR #b0000000000010010 #b010 #b0000 ))
(rule (REC_ALL_INC #b0000000000010010 #b010 #b0000 ))

;   store i8 %frombool4, i8* %p1.addr, align 1
(rule (store_assign #b0000000000010010 #b0000000000000101))
;   %0 = load i8* %r1.addr, align 1
(rule (load_assign #b0000000000010100 #b0000000000000001))
;   %tobool = trunc i8 %0 to i1
(trunc ( #b0000000000010101 #b0000000000010100))
;   %conv = zext i1 %tobool to i32
(zext ( #b0000000000010110 #b0000000000010101))
;   %1 = load i8* %k1.addr, align 1
(rule (load_assign #b0000000000010111 #b0000000000000011))
;   %tobool5 = trunc i8 %1 to i1
(trunc ( #b0000000000011000 #b0000000000010111))
;   %conv6 = zext i1 %tobool5 to i32
(zext ( #b0000000000011001 #b0000000000011000))
;   %xor = xor i32 %conv, %conv6
(rule (xor_assign_left #b0000000000011010 #b0000000000010110))
;   %xor = xor i32 %conv, %conv6
(rule (xor_assign_right #b0000000000011010 #b0000000000011001))
;   %frombool8 = zext i1 %tobool7 to i8
(zext ( #b0000000000011100 #b0000000000011011))
;   store i8 %frombool8, i8* %c1, align 1
(rule (store_assign #b0000000000011100 #b0000000000000110))
;   %2 = load i8* %r2.addr, align 1
(rule (load_assign #b0000000000011110 #b0000000000000010))
;   %tobool9 = trunc i8 %2 to i1
(trunc ( #b0000000000011111 #b0000000000011110))
;   %conv10 = zext i1 %tobool9 to i32
(zext ( #b0000000000100000 #b0000000000011111))
;   %3 = load i8* %k2.addr, align 1
(rule (load_assign #b0000000000100001 #b0000000000000100))
;   %tobool11 = trunc i8 %3 to i1
(trunc ( #b0000000000100010 #b0000000000100001))
;   %conv12 = zext i1 %tobool11 to i32
(zext ( #b0000000000100011 #b0000000000100010))
;   %xor13 = xor i32 %conv10, %conv12
(rule (xor_assign_left #b0000000000100100 #b0000000000100000))
;   %xor13 = xor i32 %conv10, %conv12
(rule (xor_assign_right #b0000000000100100 #b0000000000100011))
;   %frombool15 = zext i1 %tobool14 to i8
(zext ( #b0000000000100110 #b0000000000100101))
;   store i8 %frombool15, i8* %c2, align 1
(rule (store_assign #b0000000000100110 #b0000000000000111))
;   %4 = load i8* %p1.addr, align 1
(rule (load_assign #b0000000000101000 #b0000000000000101))
;   %tobool16 = trunc i8 %4 to i1
(trunc ( #b0000000000101001 #b0000000000101000))
;   %conv17 = zext i1 %tobool16 to i32
(zext ( #b0000000000101010 #b0000000000101001))
;   %5 = load i8* %c1, align 1
(rule (load_assign #b0000000000101011 #b0000000000000110))
;   %tobool18 = trunc i8 %5 to i1
(trunc ( #b0000000000101100 #b0000000000101011))
;   %conv19 = zext i1 %tobool18 to i32
(zext ( #b0000000000101101 #b0000000000101100))
;   %and = and i32 %conv17, %conv19
(rule (andor_assign_left #b0000000000101110 #b0000000000101010))
;   %and = and i32 %conv17, %conv19
(rule (andor_assign_right #b0000000000101110 #b0000000000101101))
;   %frombool21 = zext i1 %tobool20 to i8
(zext ( #b0000000000110000 #b0000000000101111))
;   store i8 %frombool21, i8* %c3, align 1
(rule (store_assign #b0000000000110000 #b0000000000001000))
;   %6 = load i8* %c3, align 1
(rule (load_assign #b0000000000110010 #b0000000000001000))
;   %tobool22 = trunc i8 %6 to i1
(trunc ( #b0000000000110011 #b0000000000110010))
;   %conv23 = zext i1 %tobool22 to i32
(zext ( #b0000000000110100 #b0000000000110011))
;   %7 = load i8* %c2, align 1
(rule (load_assign #b0000000000110101 #b0000000000000111))
;   %tobool24 = trunc i8 %7 to i1
(trunc ( #b0000000000110110 #b0000000000110101))
;   %conv25 = zext i1 %tobool24 to i32
(zext ( #b0000000000110111 #b0000000000110110))
;   %or = or i32 %conv23, %conv25
(rule (andor_assign_left #b0000000000111000 #b0000000000110100))
;   %or = or i32 %conv23, %conv25
(rule (andor_assign_right #b0000000000111000 #b0000000000110111))
;   %frombool27 = zext i1 %tobool26 to i8
(zext ( #b0000000000111010 #b0000000000111001))
;   store i8 %frombool27, i8* %c4, align 1
(rule (store_assign #b0000000000111010 #b0000000000001001))
;   %8 = load i8* %c4, align 1
(rule (load_assign #b0000000000111100 #b0000000000001001))
;   %tobool28 = trunc i8 %8 to i1
(trunc ( #b0000000000111101 #b0000000000111100))
;###### End Facts
