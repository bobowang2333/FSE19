; ModuleID = 'test.c'
target datalayout = "e-m:o-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.11.0"

; Function Attrs: nounwind ssp uwtable
define i32 @leak(i32 %i1, i32 %i2, i32 %key, i32 %i3) #0 {
entry:
  %i1.addr = alloca i32, align 4
  %i2.addr = alloca i32, align 4
  %key.addr = alloca i32, align 4
  %i3.addr = alloca i32, align 4
  %n1 = alloca i32, align 4
  %n2 = alloca i32, align 4
  %n3 = alloca i32, align 4
  store i32 %i1, i32* %i1.addr, align 4
  store i32 %i2, i32* %i2.addr, align 4
  store i32 %key, i32* %key.addr, align 4
  store i32 %i3, i32* %i3.addr, align 4
  %0 = load i32* %i1.addr, align 4
  %1 = load i32* %i2.addr, align 4
  %xor = xor i32 %0, %1
  store i32 %xor, i32* %n1, align 4
  %2 = load i32* %n1, align 4
  %3 = load i32* %key.addr, align 4
  %xor1 = xor i32 %2, %3
  store i32 %xor1, i32* %n2, align 4
  %4 = load i32* %n2, align 4
  %5 = load i32* %i3.addr, align 4
  %and = and i32 %4, %5
  store i32 %and, i32* %n3, align 4
  %6 = load i32* %n3, align 4
  ret i32 %6
}

; Function Attrs: nounwind ssp uwtable
define i32 @main() #0 {
entry:
  %retval = alloca i32, align 4
  %i1 = alloca i32, align 4
  %i2 = alloca i32, align 4
  %i3 = alloca i32, align 4
  %i4 = alloca i32, align 4
  %res = alloca i32, align 4
  store i32 0, i32* %retval
  store i32 1, i32* %i1, align 4
  store i32 0, i32* %i2, align 4
  store i32 0, i32* %i3, align 4
  store i32 1, i32* %i4, align 4
  %0 = load i32* %i1, align 4
  %1 = load i32* %i2, align 4
  %2 = load i32* %i3, align 4
  %3 = load i32* %i4, align 4
  %call = call i32 @leak(i32 %0, i32 %1, i32 %2, i32 %3)
  store i32 %call, i32* %res, align 4
  %4 = load i32* %res, align 4
  ret i32 %4
}

attributes #0 = { nounwind ssp uwtable "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.module.flags = !{!0}
!llvm.ident = !{!1}

!0 = !{i32 1, !"PIC Level", i32 2}
!1 = !{!"clang version 3.6.0 (tags/RELEASE_360/final)"}
