; ModuleID = 'test_vectors.c'
target datalayout = "e-m:o-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.11.0"

@expectedPlaintext = global [8 x i8] c"\EF\CD\AB\89gE#\01", align 1
@expectedKey = global [10 x i8] c"\11\003\22UDwf\99\88", align 1
@expectedCiphertext = global [8 x i8] c"V@\F85\99\FF+\8D", align 1
@.str = private unnamed_addr constant [4 x i8] c"%x\0A\00", align 1
@.str1 = private unnamed_addr constant [10 x i8] c"SUCCESS!\0A\00", align 1
@.str2 = private unnamed_addr constant [10 x i8] c"FAILURE!\0A\00", align 1

; Function Attrs: nounwind ssp uwtable
define i32 @main() #0 {
entry:
  %retval = alloca i32, align 4
  %roundKeys = alloca i8*, align 8
  %round_key = alloca i8, align 1
  %saved_stack = alloca i8*
  %i = alloca i32, align 4
  store i32 0, i32* %retval
  store i8 104, i8* %round_key, align 1
  %0 = load i8* %round_key, align 1
  %1 = zext i8 %0 to i64
  %2 = call i8* @llvm.stacksave()
  store i8* %2, i8** %saved_stack
  %vla = alloca i8, i64 %1, align 16
  store i8* %vla, i8** %roundKeys, align 8
  %3 = load i8** %roundKeys, align 8
  call void @RunEncryptionKeySchedule(i8* getelementptr inbounds ([10 x i8]* @expectedKey, i32 0, i32 0), i8* %3)
  %4 = load i8** %roundKeys, align 8
  call void @Encrypt(i8* getelementptr inbounds ([8 x i8]* @expectedPlaintext, i32 0, i32 0), i8* %4)
  store i32 0, i32* %i, align 4
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %entry
  %5 = load i32* %i, align 4
  %cmp = icmp ult i32 %5, 8
  br i1 %cmp, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %6 = load i32* %i, align 4
  %idxprom = zext i32 %6 to i64
  %arrayidx = getelementptr inbounds [8 x i8]* @expectedPlaintext, i32 0, i64 %idxprom
  %7 = load i8* %arrayidx, align 1
  %conv = zext i8 %7 to i32
  %and = and i32 %conv, 255
  %call = call i32 (i8*, ...)* @printf(i8* getelementptr inbounds ([4 x i8]* @.str, i32 0, i32 0), i32 %and)
  br label %for.inc

for.inc:                                          ; preds = %for.body
  %8 = load i32* %i, align 4
  %inc = add i32 %8, 1
  store i32 %inc, i32* %i, align 4
  br label %for.cond

for.end:                                          ; preds = %for.cond
  %call1 = call i32 @memcmp(i8* getelementptr inbounds ([8 x i8]* @expectedCiphertext, i32 0, i32 0), i8* getelementptr inbounds ([8 x i8]* @expectedPlaintext, i32 0, i32 0), i64 8)
  %cmp2 = icmp eq i32 0, %call1
  br i1 %cmp2, label %if.then, label %if.else

if.then:                                          ; preds = %for.end
  %call4 = call i32 (i8*, ...)* @printf(i8* getelementptr inbounds ([10 x i8]* @.str1, i32 0, i32 0))
  br label %if.end

if.else:                                          ; preds = %for.end
  %call5 = call i32 (i8*, ...)* @printf(i8* getelementptr inbounds ([10 x i8]* @.str2, i32 0, i32 0))
  br label %if.end

if.end:                                           ; preds = %if.else, %if.then
  %9 = load i8** %saved_stack
  call void @llvm.stackrestore(i8* %9)
  %10 = load i32* %retval
  ret i32 %10
}

; Function Attrs: nounwind
declare i8* @llvm.stacksave() #1

declare void @RunEncryptionKeySchedule(i8*, i8*) #2

declare void @Encrypt(i8*, i8*) #2

declare i32 @printf(i8*, ...) #2

declare i32 @memcmp(i8*, i8*, i64) #2

; Function Attrs: nounwind
declare void @llvm.stackrestore(i8*) #1

attributes #0 = { nounwind ssp uwtable "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { nounwind }
attributes #2 = { "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.module.flags = !{!0}
!llvm.ident = !{!1}

!0 = !{i32 1, !"PIC Level", i32 2}
!1 = !{!"clang version 3.6.0 (tags/RELEASE_360/final)"}
