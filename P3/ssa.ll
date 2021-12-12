; ModuleID = 'ssa.cpp'
target datalayout = "e-m:o-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.12.0"

; Function Attrs: nounwind ssp uwtable
define i32 @_Z7computejjj(i32 %R, i32 %x, i32 %rx) #0 {
entry:
  %R.addr = alloca i32, align 4
  %x.addr = alloca i32, align 4
  %rx.addr = alloca i32, align 4
  %T1 = alloca i32, align 4
  %T2 = alloca i32, align 4
  %T3 = alloca i32, align 4
  %R2 = alloca i32, align 4
  %A1 = alloca i32, align 4
  %A2 = alloca i32, align 4
  %A3 = alloca i32, align 4
  %X = alloca i32, align 4
  store i32 %R, i32* %R.addr, align 4
  store i32 %x, i32* %x.addr, align 4
  store i32 %rx, i32* %rx.addr, align 4
  %0 = load i32* %x.addr, align 4
  %1 = load i32* %rx.addr, align 4
  %xor = xor i32 %0, %1
  store i32 %xor, i32* %X, align 4
  %2 = load i32* %X, align 4
  %3 = load i32* %R.addr, align 4
  %xor1 = xor i32 %2, %3
  store i32 %xor1, i32* %T1, align 4
  %4 = load i32* %T1, align 4
  %5 = load i32* %R.addr, align 4
  %xor2 = xor i32 %4, %5
  store i32 %xor2, i32* %T2, align 4
  %6 = load i32* %T2, align 4
  %7 = load i32* %X, align 4
  %xor3 = xor i32 %6, %7
  store i32 %xor3, i32* %T3, align 4
  %8 = load i32* %R.addr, align 4
  %9 = load i32* %rx.addr, align 4
  %xor4 = xor i32 %8, %9
  store i32 %xor4, i32* %R2, align 4
  %10 = load i32* %X, align 4
  %11 = load i32* %R2, align 4
  %xor5 = xor i32 %10, %11
  store i32 %xor5, i32* %A1, align 4
  %12 = load i32* %A1, align 4
  %13 = load i32* %R2, align 4
  %xor6 = xor i32 %12, %13
  store i32 %xor6, i32* %A2, align 4
  %14 = load i32* %A2, align 4
  %15 = load i32* %T3, align 4
  %xor7 = xor i32 %14, %15
  store i32 %xor7, i32* %A3, align 4
  %16 = load i32* %A3, align 4
  ret i32 %16
}

attributes #0 = { nounwind ssp uwtable "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.module.flags = !{!0}
!llvm.ident = !{!1}

!0 = !{i32 1, !"PIC Level", i32 2}
!1 = !{!"clang version 3.6.0 (tags/RELEASE_360/final)"}
