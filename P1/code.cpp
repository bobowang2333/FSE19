//P1, AES shift rows
bool compute(bool r1, bool r2, bool st2_orig, bool st10_orig){
  bool r25;
  bool r24;
  bool st2;
  bool sTT2;
  bool st10;
  bool sTT10;
  st10 = st10_orig ^ r1;
  st2 = st2_orig ^ r1;
  r24  = st2 ^0;
  r25  = st10 ^0;
  sTT2 = r25 ^ 0;
  sTT10 = r24 ^ 0;
  return(sTT2 - sTT10);
} 
