; ModuleID = 'ed_constants.c'
target datalayout = "e-m:o-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.11.0"

@SBOX = constant [16 x i8] c"\0E\04\0B\02\03\08\00\09\01\0A\07\0F\06\0C\05\0D", align 16
@GF16_MUL2 = constant [16 x i8] c"\00\02\04\06\08\0A\0C\0E\03\01\07\05\0B\09\0F\0D", align 16
@GF16_MUL3 = constant [16 x i8] c"\00\03\06\05\0C\0F\0A\09\0B\08\0D\0E\07\04\01\02", align 16

!llvm.module.flags = !{!0}
!llvm.ident = !{!1}

!0 = !{i32 1, !"PIC Level", i32 2}
!1 = !{!"clang version 3.6.0 (tags/RELEASE_360/final)"}
