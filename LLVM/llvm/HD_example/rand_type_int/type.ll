; ModuleID = 'type.c'
target datalayout = "e-m:o-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.11.0"

; Function Attrs: nounwind ssp uwtable
define i32 @compute(i32 %r1, i32 %r2, i32 %r3, i32 %k) #0 {
entry:
  %r1.addr = alloca i32, align 4
  %r2.addr = alloca i32, align 4
  %r3.addr = alloca i32, align 4
  %k.addr = alloca i32, align 4
  %c1 = alloca i32, align 4
  %c2 = alloca i32, align 4
  %c3 = alloca i32, align 4
  %c4 = alloca i32, align 4
  %c5 = alloca i32, align 4
  %c6 = alloca i32, align 4
  store i32 %r1, i32* %r1.addr, align 4
  store i32 %r2, i32* %r2.addr, align 4
  store i32 %r3, i32* %r3.addr, align 4
  store i32 %k, i32* %k.addr, align 4
  %0 = load i32* %k.addr, align 4
  %1 = load i32* %r2.addr, align 4
  %xor = xor i32 %0, %1
  store i32 %xor, i32* %c1, align 4
  %2 = load i32* %r1.addr, align 4
  %3 = load i32* %r2.addr, align 4
  %xor1 = xor i32 %2, %3
  store i32 %xor1, i32* %c2, align 4
  %4 = load i32* %c2, align 4
  %5 = load i32* %c1, align 4
  %xor2 = xor i32 %4, %5
  store i32 %xor2, i32* %c3, align 4
  %6 = load i32* %c3, align 4
  %7 = load i32* %c2, align 4
  %xor3 = xor i32 %6, %7
  store i32 %xor3, i32* %c4, align 4
  %8 = load i32* %c4, align 4
  %9 = load i32* %r1.addr, align 4
  %xor4 = xor i32 %8, %9
  store i32 %xor4, i32* %c5, align 4
  %10 = load i32* %c5, align 4
  %11 = load i32* %r3.addr, align 4
  %and = and i32 %10, %11
  store i32 %and, i32* %c6, align 4
  %12 = load i32* %c6, align 4
  ret i32 %12
}

attributes #0 = { nounwind ssp uwtable "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.module.flags = !{!0}
!llvm.ident = !{!1}

!0 = !{i32 1, !"PIC Level", i32 2}
!1 = !{!"clang version 3.6.0 (tags/RELEASE_360/final)"}
