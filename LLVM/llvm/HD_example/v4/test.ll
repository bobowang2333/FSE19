; ModuleID = 'test.c'
target datalayout = "e-m:o-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.11.0"

; Function Attrs: nounwind ssp uwtable
define void @leak(i32* %i1, i32* %i2) #0 {
entry:
  %i1.addr = alloca i32*, align 8
  %i2.addr = alloca i32*, align 8
  store i32* %i1, i32** %i1.addr, align 8
  store i32* %i2, i32** %i2.addr, align 8
  %0 = load i32** %i1.addr, align 8
  %1 = load i32* %0, align 4
  %2 = load i32** %i2.addr, align 8
  %3 = load i32* %2, align 4
  %xor = xor i32 %1, %3
  %4 = load i32** %i1.addr, align 8
  store i32 %xor, i32* %4, align 4
  ret void
}

; Function Attrs: nounwind ssp uwtable
define i32 @main() #0 {
entry:
  %retval = alloca i32, align 4
  %i1 = alloca i32, align 4
  %i2 = alloca i32, align 4
  store i32 0, i32* %retval
  store i32 1, i32* %i1, align 4
  store i32 0, i32* %i2, align 4
  call void @leak(i32* %i1, i32* %i2)
  ret i32 0
}

attributes #0 = { nounwind ssp uwtable "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.module.flags = !{!0}
!llvm.ident = !{!1}

!0 = !{i32 1, !"PIC Level", i32 2}
!1 = !{!"clang version 3.6.0 (tags/RELEASE_360/final)"}
