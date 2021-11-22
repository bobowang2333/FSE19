; ModuleID = 'primitives.c'
target datalayout = "e-m:o-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.11.0"

@GF16_MUL2 = external constant [0 x i8]
@GF16_MUL3 = external constant [0 x i8]
@SBOX = external constant [0 x i8]

; Function Attrs: nounwind ssp uwtable
define zeroext i8 @polyEval(i8 zeroext %p0, i8 zeroext %p1, i8 zeroext %p2, i8 zeroext %p3) #0 {
entry:
  %p0.addr = alloca i8, align 1
  %p1.addr = alloca i8, align 1
  %p2.addr = alloca i8, align 1
  %p3.addr = alloca i8, align 1
  %y = alloca i8, align 1
  store i8 %p0, i8* %p0.addr, align 1
  store i8 %p1, i8* %p1.addr, align 1
  store i8 %p2, i8* %p2.addr, align 1
  store i8 %p3, i8* %p3.addr, align 1
  %0 = load i8* %p0.addr, align 1
  %conv = zext i8 %0 to i32
  %1 = load i8* %p1.addr, align 1
  %conv1 = zext i8 %1 to i32
  %xor = xor i32 %conv, %conv1
  %2 = load i8* %p2.addr, align 1
  %idxprom = zext i8 %2 to i64
  %arrayidx = getelementptr inbounds [0 x i8]* @GF16_MUL2, i32 0, i64 %idxprom
  %3 = load i8* %arrayidx, align 1
  %conv2 = zext i8 %3 to i32
  %xor3 = xor i32 %xor, %conv2
  %4 = load i8* %p3.addr, align 1
  %idxprom4 = zext i8 %4 to i64
  %arrayidx5 = getelementptr inbounds [0 x i8]* @GF16_MUL3, i32 0, i64 %idxprom4
  %5 = load i8* %arrayidx5, align 1
  %conv6 = zext i8 %5 to i32
  %xor7 = xor i32 %xor3, %conv6
  %conv8 = trunc i32 %xor7 to i8
  store i8 %conv8, i8* %y, align 1
  %6 = load i8* %y, align 1
  ret i8 %6
}

; Function Attrs: nounwind ssp uwtable
define zeroext i16 @F(i16 zeroext %x) #0 {
entry:
  %x.addr = alloca i16, align 2
  %x0 = alloca i8, align 1
  %x1 = alloca i8, align 1
  %x2 = alloca i8, align 1
  %x3 = alloca i8, align 1
  %y0 = alloca i8, align 1
  %y1 = alloca i8, align 1
  %y2 = alloca i8, align 1
  %y3 = alloca i8, align 1
  store i16 %x, i16* %x.addr, align 2
  %0 = load i16* %x.addr, align 2
  %conv = zext i16 %0 to i32
  %shr = ashr i32 %conv, 0
  %and = and i32 %shr, 15
  %conv1 = trunc i32 %and to i8
  store i8 %conv1, i8* %x3, align 1
  %1 = load i16* %x.addr, align 2
  %conv2 = zext i16 %1 to i32
  %shr3 = ashr i32 %conv2, 4
  %and4 = and i32 %shr3, 15
  %conv5 = trunc i32 %and4 to i8
  store i8 %conv5, i8* %x2, align 1
  %2 = load i16* %x.addr, align 2
  %conv6 = zext i16 %2 to i32
  %shr7 = ashr i32 %conv6, 8
  %and8 = and i32 %shr7, 15
  %conv9 = trunc i32 %and8 to i8
  store i8 %conv9, i8* %x1, align 1
  %3 = load i16* %x.addr, align 2
  %conv10 = zext i16 %3 to i32
  %shr11 = ashr i32 %conv10, 12
  %and12 = and i32 %shr11, 15
  %conv13 = trunc i32 %and12 to i8
  store i8 %conv13, i8* %x0, align 1
  %4 = load i8* %x3, align 1
  %idxprom = zext i8 %4 to i64
  %arrayidx = getelementptr inbounds [0 x i8]* @SBOX, i32 0, i64 %idxprom
  %5 = load i8* %arrayidx, align 1
  store i8 %5, i8* %x3, align 1
  %6 = load i8* %x2, align 1
  %idxprom14 = zext i8 %6 to i64
  %arrayidx15 = getelementptr inbounds [0 x i8]* @SBOX, i32 0, i64 %idxprom14
  %7 = load i8* %arrayidx15, align 1
  store i8 %7, i8* %x2, align 1
  %8 = load i8* %x1, align 1
  %idxprom16 = zext i8 %8 to i64
  %arrayidx17 = getelementptr inbounds [0 x i8]* @SBOX, i32 0, i64 %idxprom16
  %9 = load i8* %arrayidx17, align 1
  store i8 %9, i8* %x1, align 1
  %10 = load i8* %x0, align 1
  %idxprom18 = zext i8 %10 to i64
  %arrayidx19 = getelementptr inbounds [0 x i8]* @SBOX, i32 0, i64 %idxprom18
  %11 = load i8* %arrayidx19, align 1
  store i8 %11, i8* %x0, align 1
  %12 = load i8* %x2, align 1
  %13 = load i8* %x3, align 1
  %14 = load i8* %x0, align 1
  %15 = load i8* %x1, align 1
  %call = call zeroext i8 @polyEval(i8 zeroext %12, i8 zeroext %13, i8 zeroext %14, i8 zeroext %15)
  store i8 %call, i8* %y0, align 1
  %16 = load i8* %x3, align 1
  %17 = load i8* %x0, align 1
  %18 = load i8* %x1, align 1
  %19 = load i8* %x2, align 1
  %call20 = call zeroext i8 @polyEval(i8 zeroext %16, i8 zeroext %17, i8 zeroext %18, i8 zeroext %19)
  store i8 %call20, i8* %y1, align 1
  %20 = load i8* %x0, align 1
  %21 = load i8* %x1, align 1
  %22 = load i8* %x2, align 1
  %23 = load i8* %x3, align 1
  %call21 = call zeroext i8 @polyEval(i8 zeroext %20, i8 zeroext %21, i8 zeroext %22, i8 zeroext %23)
  store i8 %call21, i8* %y2, align 1
  %24 = load i8* %x1, align 1
  %25 = load i8* %x2, align 1
  %26 = load i8* %x3, align 1
  %27 = load i8* %x0, align 1
  %call22 = call zeroext i8 @polyEval(i8 zeroext %24, i8 zeroext %25, i8 zeroext %26, i8 zeroext %27)
  store i8 %call22, i8* %y3, align 1
  %28 = load i8* %y0, align 1
  %idxprom23 = zext i8 %28 to i64
  %arrayidx24 = getelementptr inbounds [0 x i8]* @SBOX, i32 0, i64 %idxprom23
  %29 = load i8* %arrayidx24, align 1
  store i8 %29, i8* %y0, align 1
  %30 = load i8* %y1, align 1
  %idxprom25 = zext i8 %30 to i64
  %arrayidx26 = getelementptr inbounds [0 x i8]* @SBOX, i32 0, i64 %idxprom25
  %31 = load i8* %arrayidx26, align 1
  store i8 %31, i8* %y1, align 1
  %32 = load i8* %y2, align 1
  %idxprom27 = zext i8 %32 to i64
  %arrayidx28 = getelementptr inbounds [0 x i8]* @SBOX, i32 0, i64 %idxprom27
  %33 = load i8* %arrayidx28, align 1
  store i8 %33, i8* %y2, align 1
  %34 = load i8* %y3, align 1
  %idxprom29 = zext i8 %34 to i64
  %arrayidx30 = getelementptr inbounds [0 x i8]* @SBOX, i32 0, i64 %idxprom29
  %35 = load i8* %arrayidx30, align 1
  store i8 %35, i8* %y3, align 1
  %36 = load i8* %y0, align 1
  %conv31 = zext i8 %36 to i32
  %shl = shl i32 %conv31, 12
  %37 = load i8* %y1, align 1
  %conv32 = zext i8 %37 to i32
  %shl33 = shl i32 %conv32, 8
  %or = or i32 %shl, %shl33
  %38 = load i8* %y2, align 1
  %conv34 = zext i8 %38 to i32
  %shl35 = shl i32 %conv34, 4
  %or36 = or i32 %or, %shl35
  %39 = load i8* %y3, align 1
  %conv37 = zext i8 %39 to i32
  %or38 = or i32 %or36, %conv37
  %conv39 = trunc i32 %or38 to i16
  ret i16 %conv39
}

; Function Attrs: nounwind ssp uwtable
define void @RP(i16* %x0, i16* %x1, i16* %x2, i16* %x3) #0 {
entry:
  %x0.addr = alloca i16*, align 8
  %x1.addr = alloca i16*, align 8
  %x2.addr = alloca i16*, align 8
  %x3.addr = alloca i16*, align 8
  %y0 = alloca i16, align 2
  %y1 = alloca i16, align 2
  %y2 = alloca i16, align 2
  %y3 = alloca i16, align 2
  store i16* %x0, i16** %x0.addr, align 8
  store i16* %x1, i16** %x1.addr, align 8
  store i16* %x2, i16** %x2.addr, align 8
  store i16* %x3, i16** %x3.addr, align 8
  %0 = load i16** %x1.addr, align 8
  %1 = load i16* %0, align 2
  %conv = zext i16 %1 to i32
  %and = and i32 %conv, 65280
  %2 = load i16** %x3.addr, align 8
  %3 = load i16* %2, align 2
  %conv1 = zext i16 %3 to i32
  %and2 = and i32 %conv1, 255
  %or = or i32 %and, %and2
  %conv3 = trunc i32 %or to i16
  store i16 %conv3, i16* %y0, align 2
  %4 = load i16** %x2.addr, align 8
  %5 = load i16* %4, align 2
  %conv4 = zext i16 %5 to i32
  %and5 = and i32 %conv4, 65280
  %6 = load i16** %x0.addr, align 8
  %7 = load i16* %6, align 2
  %conv6 = zext i16 %7 to i32
  %and7 = and i32 %conv6, 255
  %or8 = or i32 %and5, %and7
  %conv9 = trunc i32 %or8 to i16
  store i16 %conv9, i16* %y1, align 2
  %8 = load i16** %x3.addr, align 8
  %9 = load i16* %8, align 2
  %conv10 = zext i16 %9 to i32
  %and11 = and i32 %conv10, 65280
  %10 = load i16** %x1.addr, align 8
  %11 = load i16* %10, align 2
  %conv12 = zext i16 %11 to i32
  %and13 = and i32 %conv12, 255
  %or14 = or i32 %and11, %and13
  %conv15 = trunc i32 %or14 to i16
  store i16 %conv15, i16* %y2, align 2
  %12 = load i16** %x0.addr, align 8
  %13 = load i16* %12, align 2
  %conv16 = zext i16 %13 to i32
  %and17 = and i32 %conv16, 65280
  %14 = load i16** %x2.addr, align 8
  %15 = load i16* %14, align 2
  %conv18 = zext i16 %15 to i32
  %and19 = and i32 %conv18, 255
  %or20 = or i32 %and17, %and19
  %conv21 = trunc i32 %or20 to i16
  store i16 %conv21, i16* %y3, align 2
  %16 = load i16* %y0, align 2
  %17 = load i16** %x0.addr, align 8
  store i16 %16, i16* %17, align 2
  %18 = load i16* %y1, align 2
  %19 = load i16** %x1.addr, align 8
  store i16 %18, i16* %19, align 2
  %20 = load i16* %y2, align 2
  %21 = load i16** %x2.addr, align 8
  store i16 %20, i16* %21, align 2
  %22 = load i16* %y3, align 2
  %23 = load i16** %x3.addr, align 8
  store i16 %22, i16* %23, align 2
  ret void
}

attributes #0 = { nounwind ssp uwtable "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.module.flags = !{!0}
!llvm.ident = !{!1}

!0 = !{i32 1, !"PIC Level", i32 2}
!1 = !{!"clang version 3.6.0 (tags/RELEASE_360/final)"}
