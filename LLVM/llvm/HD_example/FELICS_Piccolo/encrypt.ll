; ModuleID = 'encrypt.c'
target datalayout = "e-m:o-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.11.0"

; Function Attrs: nounwind ssp uwtable
define void @Encrypt(i8* %block, i8* %roundKeys) #0 {
entry:
  %block.addr = alloca i8*, align 8
  %roundKeys.addr = alloca i8*, align 8
  %i = alloca i8, align 1
  %x3 = alloca i16*, align 8
  %x2 = alloca i16*, align 8
  %x1 = alloca i16*, align 8
  %x0 = alloca i16*, align 8
  %rk = alloca i16*, align 8
  store i8* %block, i8** %block.addr, align 8
  store i8* %roundKeys, i8** %roundKeys.addr, align 8
  %0 = load i8** %block.addr, align 8
  %1 = bitcast i8* %0 to i16*
  store i16* %1, i16** %x3, align 8
  %2 = load i16** %x3, align 8
  %add.ptr = getelementptr inbounds i16* %2, i64 1
  store i16* %add.ptr, i16** %x2, align 8
  %3 = load i16** %x3, align 8
  %add.ptr1 = getelementptr inbounds i16* %3, i64 2
  store i16* %add.ptr1, i16** %x1, align 8
  %4 = load i16** %x3, align 8
  %add.ptr2 = getelementptr inbounds i16* %4, i64 3
  store i16* %add.ptr2, i16** %x0, align 8
  %5 = load i8** %roundKeys.addr, align 8
  %6 = bitcast i8* %5 to i16*
  store i16* %6, i16** %rk, align 8
  %7 = load i16** %rk, align 8
  %arrayidx = getelementptr inbounds i16* %7, i64 51
  %8 = load i16* %arrayidx, align 2
  %conv = zext i16 %8 to i32
  %9 = load i16** %x2, align 8
  %10 = load i16* %9, align 2
  %conv3 = zext i16 %10 to i32
  %xor = xor i32 %conv3, %conv
  %conv4 = trunc i32 %xor to i16
  store i16 %conv4, i16* %9, align 2
  %11 = load i16** %rk, align 8
  %arrayidx5 = getelementptr inbounds i16* %11, i64 50
  %12 = load i16* %arrayidx5, align 2
  %conv6 = zext i16 %12 to i32
  %13 = load i16** %x0, align 8
  %14 = load i16* %13, align 2
  %conv7 = zext i16 %14 to i32
  %xor8 = xor i32 %conv7, %conv6
  %conv9 = trunc i32 %xor8 to i16
  store i16 %conv9, i16* %13, align 2
  store i8 0, i8* %i, align 1
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %entry
  %15 = load i8* %i, align 1
  %conv10 = zext i8 %15 to i32
  %cmp = icmp slt i32 %conv10, 24
  br i1 %cmp, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %16 = load i16** %x1, align 8
  %17 = load i16* %16, align 2
  %conv12 = zext i16 %17 to i32
  %18 = load i16** %x0, align 8
  %19 = load i16* %18, align 2
  %call = call zeroext i16 @F(i16 zeroext %19)
  %conv13 = zext i16 %call to i32
  %xor14 = xor i32 %conv12, %conv13
  %20 = load i8* %i, align 1
  %conv15 = zext i8 %20 to i32
  %mul = mul nsw i32 2, %conv15
  %idxprom = sext i32 %mul to i64
  %21 = load i16** %rk, align 8
  %arrayidx16 = getelementptr inbounds i16* %21, i64 %idxprom
  %22 = load i16* %arrayidx16, align 2
  %conv17 = zext i16 %22 to i32
  %xor18 = xor i32 %xor14, %conv17
  %conv19 = trunc i32 %xor18 to i16
  %23 = load i16** %x1, align 8
  store i16 %conv19, i16* %23, align 2
  %24 = load i16** %x3, align 8
  %25 = load i16* %24, align 2
  %conv20 = zext i16 %25 to i32
  %26 = load i16** %x2, align 8
  %27 = load i16* %26, align 2
  %call21 = call zeroext i16 @F(i16 zeroext %27)
  %conv22 = zext i16 %call21 to i32
  %xor23 = xor i32 %conv20, %conv22
  %28 = load i8* %i, align 1
  %conv24 = zext i8 %28 to i32
  %mul25 = mul nsw i32 2, %conv24
  %add = add nsw i32 %mul25, 1
  %idxprom26 = sext i32 %add to i64
  %29 = load i16** %rk, align 8
  %arrayidx27 = getelementptr inbounds i16* %29, i64 %idxprom26
  %30 = load i16* %arrayidx27, align 2
  %conv28 = zext i16 %30 to i32
  %xor29 = xor i32 %xor23, %conv28
  %conv30 = trunc i32 %xor29 to i16
  %31 = load i16** %x3, align 8
  store i16 %conv30, i16* %31, align 2
  %32 = load i16** %x0, align 8
  %33 = load i16** %x1, align 8
  %34 = load i16** %x2, align 8
  %35 = load i16** %x3, align 8
  call void @RP(i16* %32, i16* %33, i16* %34, i16* %35)
  br label %for.inc

for.inc:                                          ; preds = %for.body
  %36 = load i8* %i, align 1
  %inc = add i8 %36, 1
  store i8 %inc, i8* %i, align 1
  br label %for.cond

for.end:                                          ; preds = %for.cond
  %37 = load i16** %x1, align 8
  %38 = load i16* %37, align 2
  %conv31 = zext i16 %38 to i32
  %39 = load i16** %x0, align 8
  %40 = load i16* %39, align 2
  %call32 = call zeroext i16 @F(i16 zeroext %40)
  %conv33 = zext i16 %call32 to i32
  %xor34 = xor i32 %conv31, %conv33
  %41 = load i16** %rk, align 8
  %arrayidx35 = getelementptr inbounds i16* %41, i64 48
  %42 = load i16* %arrayidx35, align 2
  %conv36 = zext i16 %42 to i32
  %xor37 = xor i32 %xor34, %conv36
  %conv38 = trunc i32 %xor37 to i16
  %43 = load i16** %x1, align 8
  store i16 %conv38, i16* %43, align 2
  %44 = load i16** %x3, align 8
  %45 = load i16* %44, align 2
  %conv39 = zext i16 %45 to i32
  %46 = load i16** %x2, align 8
  %47 = load i16* %46, align 2
  %call40 = call zeroext i16 @F(i16 zeroext %47)
  %conv41 = zext i16 %call40 to i32
  %xor42 = xor i32 %conv39, %conv41
  %48 = load i16** %rk, align 8
  %arrayidx43 = getelementptr inbounds i16* %48, i64 49
  %49 = load i16* %arrayidx43, align 2
  %conv44 = zext i16 %49 to i32
  %xor45 = xor i32 %xor42, %conv44
  %conv46 = trunc i32 %xor45 to i16
  %50 = load i16** %x3, align 8
  store i16 %conv46, i16* %50, align 2
  %51 = load i16** %rk, align 8
  %arrayidx47 = getelementptr inbounds i16* %51, i64 52
  %52 = load i16* %arrayidx47, align 2
  %conv48 = zext i16 %52 to i32
  %53 = load i16** %x0, align 8
  %54 = load i16* %53, align 2
  %conv49 = zext i16 %54 to i32
  %xor50 = xor i32 %conv49, %conv48
  %conv51 = trunc i32 %xor50 to i16
  store i16 %conv51, i16* %53, align 2
  %55 = load i16** %rk, align 8
  %arrayidx52 = getelementptr inbounds i16* %55, i64 53
  %56 = load i16* %arrayidx52, align 2
  %conv53 = zext i16 %56 to i32
  %57 = load i16** %x2, align 8
  %58 = load i16* %57, align 2
  %conv54 = zext i16 %58 to i32
  %xor55 = xor i32 %conv54, %conv53
  %conv56 = trunc i32 %xor55 to i16
  store i16 %conv56, i16* %57, align 2
  ret void
}

declare zeroext i16 @F(i16 zeroext) #1

declare void @RP(i16*, i16*, i16*, i16*) #1

attributes #0 = { nounwind ssp uwtable "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.module.flags = !{!0}
!llvm.ident = !{!1}

!0 = !{i32 1, !"PIC Level", i32 2}
!1 = !{!"clang version 3.6.0 (tags/RELEASE_360/final)"}
