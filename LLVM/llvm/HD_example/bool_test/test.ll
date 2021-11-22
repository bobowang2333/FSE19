; ModuleID = 'test.cpp'
target datalayout = "e-m:o-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.11.0"

; Function Attrs: nounwind ssp uwtable
define zeroext i1 @_Z7computebbbbb(i1 zeroext %r1, i1 zeroext %r2, i1 zeroext %k1, i1 zeroext %k2, i1 zeroext %p1) #0 {
entry:
  %r1.addr = alloca i8, align 1
  %r2.addr = alloca i8, align 1
  %k1.addr = alloca i8, align 1
  %k2.addr = alloca i8, align 1
  %p1.addr = alloca i8, align 1
  %c1 = alloca i8, align 1
  %c2 = alloca i8, align 1
  %c3 = alloca i8, align 1
  %c4 = alloca i8, align 1
  %frombool = zext i1 %r1 to i8
  store i8 %frombool, i8* %r1.addr, align 1
  %frombool1 = zext i1 %r2 to i8
  store i8 %frombool1, i8* %r2.addr, align 1
  %frombool2 = zext i1 %k1 to i8
  store i8 %frombool2, i8* %k1.addr, align 1
  %frombool3 = zext i1 %k2 to i8
  store i8 %frombool3, i8* %k2.addr, align 1
  %frombool4 = zext i1 %p1 to i8
  store i8 %frombool4, i8* %p1.addr, align 1
  %0 = load i8* %r1.addr, align 1
  %tobool = trunc i8 %0 to i1
  %conv = zext i1 %tobool to i32
  %1 = load i8* %k1.addr, align 1
  %tobool5 = trunc i8 %1 to i1
  %conv6 = zext i1 %tobool5 to i32
  %xor = xor i32 %conv, %conv6
  %tobool7 = icmp ne i32 %xor, 0
  %frombool8 = zext i1 %tobool7 to i8
  store i8 %frombool8, i8* %c1, align 1
  %2 = load i8* %r2.addr, align 1
  %tobool9 = trunc i8 %2 to i1
  %conv10 = zext i1 %tobool9 to i32
  %3 = load i8* %k2.addr, align 1
  %tobool11 = trunc i8 %3 to i1
  %conv12 = zext i1 %tobool11 to i32
  %xor13 = xor i32 %conv10, %conv12
  %tobool14 = icmp ne i32 %xor13, 0
  %frombool15 = zext i1 %tobool14 to i8
  store i8 %frombool15, i8* %c2, align 1
  %4 = load i8* %p1.addr, align 1
  %tobool16 = trunc i8 %4 to i1
  %conv17 = zext i1 %tobool16 to i32
  %5 = load i8* %c1, align 1
  %tobool18 = trunc i8 %5 to i1
  %conv19 = zext i1 %tobool18 to i32
  %and = and i32 %conv17, %conv19
  %tobool20 = icmp ne i32 %and, 0
  %frombool21 = zext i1 %tobool20 to i8
  store i8 %frombool21, i8* %c3, align 1
  %6 = load i8* %c3, align 1
  %tobool22 = trunc i8 %6 to i1
  %conv23 = zext i1 %tobool22 to i32
  %7 = load i8* %c2, align 1
  %tobool24 = trunc i8 %7 to i1
  %conv25 = zext i1 %tobool24 to i32
  %or = or i32 %conv23, %conv25
  %tobool26 = icmp ne i32 %or, 0
  %frombool27 = zext i1 %tobool26 to i8
  store i8 %frombool27, i8* %c4, align 1
  %8 = load i8* %c4, align 1
  %tobool28 = trunc i8 %8 to i1
  ret i1 %tobool28
}

attributes #0 = { nounwind ssp uwtable "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.module.flags = !{!0}
!llvm.ident = !{!1}

!0 = !{i32 1, !"PIC Level", i32 2}
!1 = !{!"clang version 3.6.0 (tags/RELEASE_360/final)"}
