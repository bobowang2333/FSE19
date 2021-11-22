; ModuleID = 'encryption_key_schedule.c'
target datalayout = "e-m:o-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.11.0"

@CON80 = external constant [0 x i32]

; Function Attrs: nounwind ssp uwtable
define void @RunEncryptionKeySchedule(i8* %key, i8* %roundKeys) #0 {
entry:
  %key.addr = alloca i8*, align 8
  %roundKeys.addr = alloca i8*, align 8
  %i = alloca i8, align 1
  %m = alloca i8, align 1
  %mk = alloca i16*, align 8
  %_rk = alloca i32, align 4
  %rk = alloca i16*, align 8
  %wk = alloca i16*, align 8
  store i8* %key, i8** %key.addr, align 8
  store i8* %roundKeys, i8** %roundKeys.addr, align 8
  %0 = load i8** %key.addr, align 8
  %1 = bitcast i8* %0 to i16*
  store i16* %1, i16** %mk, align 8
  %2 = load i8** %roundKeys.addr, align 8
  %3 = bitcast i8* %2 to i16*
  store i16* %3, i16** %rk, align 8
  %4 = load i8** %roundKeys.addr, align 8
  %arrayidx = getelementptr inbounds i8* %4, i64 100
  %5 = bitcast i8* %arrayidx to i16*
  store i16* %5, i16** %wk, align 8
  %6 = load i16** %mk, align 8
  %arrayidx1 = getelementptr inbounds i16* %6, i64 0
  %7 = load i16* %arrayidx1, align 2
  %conv = zext i16 %7 to i32
  %and = and i32 %conv, 65280
  %8 = load i16** %mk, align 8
  %arrayidx2 = getelementptr inbounds i16* %8, i64 1
  %9 = load i16* %arrayidx2, align 2
  %conv3 = zext i16 %9 to i32
  %and4 = and i32 %conv3, 255
  %or = or i32 %and, %and4
  %conv5 = trunc i32 %or to i16
  %10 = load i16** %wk, align 8
  %arrayidx6 = getelementptr inbounds i16* %10, i64 0
  store i16 %conv5, i16* %arrayidx6, align 2
  %11 = load i16** %mk, align 8
  %arrayidx7 = getelementptr inbounds i16* %11, i64 1
  %12 = load i16* %arrayidx7, align 2
  %conv8 = zext i16 %12 to i32
  %and9 = and i32 %conv8, 65280
  %13 = load i16** %mk, align 8
  %arrayidx10 = getelementptr inbounds i16* %13, i64 0
  %14 = load i16* %arrayidx10, align 2
  %conv11 = zext i16 %14 to i32
  %and12 = and i32 %conv11, 255
  %or13 = or i32 %and9, %and12
  %conv14 = trunc i32 %or13 to i16
  %15 = load i16** %wk, align 8
  %arrayidx15 = getelementptr inbounds i16* %15, i64 1
  store i16 %conv14, i16* %arrayidx15, align 2
  %16 = load i16** %mk, align 8
  %arrayidx16 = getelementptr inbounds i16* %16, i64 4
  %17 = load i16* %arrayidx16, align 2
  %conv17 = zext i16 %17 to i32
  %and18 = and i32 %conv17, 65280
  %18 = load i16** %mk, align 8
  %arrayidx19 = getelementptr inbounds i16* %18, i64 3
  %19 = load i16* %arrayidx19, align 2
  %conv20 = zext i16 %19 to i32
  %and21 = and i32 %conv20, 255
  %or22 = or i32 %and18, %and21
  %conv23 = trunc i32 %or22 to i16
  %20 = load i16** %wk, align 8
  %arrayidx24 = getelementptr inbounds i16* %20, i64 2
  store i16 %conv23, i16* %arrayidx24, align 2
  %21 = load i16** %mk, align 8
  %arrayidx25 = getelementptr inbounds i16* %21, i64 3
  %22 = load i16* %arrayidx25, align 2
  %conv26 = zext i16 %22 to i32
  %and27 = and i32 %conv26, 65280
  %23 = load i16** %mk, align 8
  %arrayidx28 = getelementptr inbounds i16* %23, i64 4
  %24 = load i16* %arrayidx28, align 2
  %conv29 = zext i16 %24 to i32
  %and30 = and i32 %conv29, 255
  %or31 = or i32 %and27, %and30
  %conv32 = trunc i32 %or31 to i16
  %25 = load i16** %wk, align 8
  %arrayidx33 = getelementptr inbounds i16* %25, i64 3
  store i16 %conv32, i16* %arrayidx33, align 2
  store i8 0, i8* %m, align 1
  store i8 0, i8* %i, align 1
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %entry
  %26 = load i8* %i, align 1
  %conv34 = zext i8 %26 to i32
  %cmp = icmp slt i32 %conv34, 25
  br i1 %cmp, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %27 = load i8* %i, align 1
  %idxprom = zext i8 %27 to i64
  %arrayidx36 = getelementptr inbounds [0 x i32]* @CON80, i32 0, i64 %idxprom
  %28 = load i32* %arrayidx36, align 4
  store i32 %28, i32* %_rk, align 4
  %29 = load i8* %m, align 1
  %conv37 = zext i8 %29 to i32
  switch i32 %conv37, label %sw.epilog [
    i32 0, label %sw.bb
    i32 2, label %sw.bb
    i32 3, label %sw.bb39
    i32 1, label %sw.bb46
    i32 4, label %sw.bb46
  ]

sw.bb:                                            ; preds = %for.body, %for.body
  %30 = load i16** %mk, align 8
  %arrayidx38 = getelementptr inbounds i16* %30, i64 2
  %31 = bitcast i16* %arrayidx38 to i32*
  %32 = load i32* %31, align 4
  %33 = load i32* %_rk, align 4
  %xor = xor i32 %33, %32
  store i32 %xor, i32* %_rk, align 4
  br label %sw.epilog

sw.bb39:                                          ; preds = %for.body
  %34 = load i16** %mk, align 8
  %arrayidx40 = getelementptr inbounds i16* %34, i64 4
  %35 = load i16* %arrayidx40, align 2
  %conv41 = zext i16 %35 to i32
  %shl = shl i32 %conv41, 16
  %36 = load i16** %mk, align 8
  %arrayidx42 = getelementptr inbounds i16* %36, i64 4
  %37 = load i16* %arrayidx42, align 2
  %conv43 = zext i16 %37 to i32
  %or44 = or i32 %shl, %conv43
  %38 = load i32* %_rk, align 4
  %xor45 = xor i32 %38, %or44
  store i32 %xor45, i32* %_rk, align 4
  br label %sw.epilog

sw.bb46:                                          ; preds = %for.body, %for.body
  %39 = load i16** %mk, align 8
  %arrayidx47 = getelementptr inbounds i16* %39, i64 0
  %40 = bitcast i16* %arrayidx47 to i32*
  %41 = load i32* %40, align 4
  %42 = load i32* %_rk, align 4
  %xor48 = xor i32 %42, %41
  store i32 %xor48, i32* %_rk, align 4
  br label %sw.epilog

sw.epilog:                                        ; preds = %for.body, %sw.bb46, %sw.bb39, %sw.bb
  %43 = load i32* %_rk, align 4
  %44 = load i8* %i, align 1
  %conv49 = zext i8 %44 to i32
  %mul = mul nsw i32 2, %conv49
  %idxprom50 = sext i32 %mul to i64
  %45 = load i16** %rk, align 8
  %arrayidx51 = getelementptr inbounds i16* %45, i64 %idxprom50
  %46 = bitcast i16* %arrayidx51 to i32*
  store i32 %43, i32* %46, align 4
  %47 = load i8* %m, align 1
  %conv52 = zext i8 %47 to i32
  %cmp53 = icmp eq i32 %conv52, 4
  br i1 %cmp53, label %if.then, label %if.else

if.then:                                          ; preds = %sw.epilog
  store i8 0, i8* %m, align 1
  br label %if.end

if.else:                                          ; preds = %sw.epilog
  %48 = load i8* %m, align 1
  %inc = add i8 %48, 1
  store i8 %inc, i8* %m, align 1
  br label %if.end

if.end:                                           ; preds = %if.else, %if.then
  br label %for.inc

for.inc:                                          ; preds = %if.end
  %49 = load i8* %i, align 1
  %inc55 = add i8 %49, 1
  store i8 %inc55, i8* %i, align 1
  br label %for.cond

for.end:                                          ; preds = %for.cond
  ret void
}

attributes #0 = { nounwind ssp uwtable "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.module.flags = !{!0}
!llvm.ident = !{!1}

!0 = !{i32 1, !"PIC Level", i32 2}
!1 = !{!"clang version 3.6.0 (tags/RELEASE_360/final)"}
