; ModuleID = 'type.c'
target datalayout = "e-m:o-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.11.0"

; Function Attrs: nounwind ssp uwtable
define zeroext i1 @compute(i1 zeroext %r1, i1 zeroext %r2, i1 zeroext %r3, i1 zeroext %k) #0 {
entry:
  %r1.addr = alloca i8, align 1
  %r2.addr = alloca i8, align 1
  %r3.addr = alloca i8, align 1
  %k.addr = alloca i8, align 1
  %c1 = alloca i8, align 1
  %c2 = alloca i8, align 1
  %c3 = alloca i8, align 1
  %c4 = alloca i8, align 1
  %c5 = alloca i8, align 1
  %c6 = alloca i8, align 1
  %frombool = zext i1 %r1 to i8
  store i8 %frombool, i8* %r1.addr, align 1
  %frombool1 = zext i1 %r2 to i8
  store i8 %frombool1, i8* %r2.addr, align 1
  %frombool2 = zext i1 %r3 to i8
  store i8 %frombool2, i8* %r3.addr, align 1
  %frombool3 = zext i1 %k to i8
  store i8 %frombool3, i8* %k.addr, align 1
  %0 = load i8* %k.addr, align 1
  %tobool = trunc i8 %0 to i1
  %conv = zext i1 %tobool to i32
  %1 = load i8* %r2.addr, align 1
  %tobool4 = trunc i8 %1 to i1
  %conv5 = zext i1 %tobool4 to i32
  %xor = xor i32 %conv, %conv5
  %tobool6 = icmp ne i32 %xor, 0
  %frombool7 = zext i1 %tobool6 to i8
  store i8 %frombool7, i8* %c1, align 1
  %2 = load i8* %r1.addr, align 1
  %tobool8 = trunc i8 %2 to i1
  %conv9 = zext i1 %tobool8 to i32
  %3 = load i8* %r2.addr, align 1
  %tobool10 = trunc i8 %3 to i1
  %conv11 = zext i1 %tobool10 to i32
  %xor12 = xor i32 %conv9, %conv11
  %tobool13 = icmp ne i32 %xor12, 0
  %frombool14 = zext i1 %tobool13 to i8
  store i8 %frombool14, i8* %c2, align 1
  %4 = load i8* %c2, align 1
  %tobool15 = trunc i8 %4 to i1
  %conv16 = zext i1 %tobool15 to i32
  %5 = load i8* %c1, align 1
  %tobool17 = trunc i8 %5 to i1
  %conv18 = zext i1 %tobool17 to i32
  %xor19 = xor i32 %conv16, %conv18
  %tobool20 = icmp ne i32 %xor19, 0
  %frombool21 = zext i1 %tobool20 to i8
  store i8 %frombool21, i8* %c3, align 1
  %6 = load i8* %c3, align 1
  %tobool22 = trunc i8 %6 to i1
  %conv23 = zext i1 %tobool22 to i32
  %7 = load i8* %c2, align 1
  %tobool24 = trunc i8 %7 to i1
  %conv25 = zext i1 %tobool24 to i32
  %xor26 = xor i32 %conv23, %conv25
  %tobool27 = icmp ne i32 %xor26, 0
  %frombool28 = zext i1 %tobool27 to i8
  store i8 %frombool28, i8* %c4, align 1
  %8 = load i8* %c4, align 1
  %tobool29 = trunc i8 %8 to i1
  %conv30 = zext i1 %tobool29 to i32
  %9 = load i8* %r1.addr, align 1
  %tobool31 = trunc i8 %9 to i1
  %conv32 = zext i1 %tobool31 to i32
  %xor33 = xor i32 %conv30, %conv32
  %tobool34 = icmp ne i32 %xor33, 0
  %frombool35 = zext i1 %tobool34 to i8
  store i8 %frombool35, i8* %c5, align 1
  %10 = load i8* %c5, align 1
  %tobool36 = trunc i8 %10 to i1
  %conv37 = zext i1 %tobool36 to i32
  %11 = load i8* %r3.addr, align 1
  %tobool38 = trunc i8 %11 to i1
  %conv39 = zext i1 %tobool38 to i32
  %and = and i32 %conv37, %conv39
  %tobool40 = icmp ne i32 %and, 0
  %frombool41 = zext i1 %tobool40 to i8
  store i8 %frombool41, i8* %c6, align 1
  %12 = load i8* %c6, align 1
  %tobool42 = trunc i8 %12 to i1
  ret i1 %tobool42
}

attributes #0 = { nounwind ssp uwtable "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.module.flags = !{!0}
!llvm.ident = !{!1}

!0 = !{i32 1, !"PIC Level", i32 2}
!1 = !{!"clang version 3.6.0 (tags/RELEASE_360/final)"}
