int SecMult(int a, int b, int a0, int b0, int r0_01){
    int a1;
    int b1;
    int c0, c1;
    int r0_10, p0_01, p0_10;
    // (* Presharing a *)
    // a0 = $distr;
    a1 = a ^ a0;
    // (* Presharing b *)
    // b0 = $distr;
    b1 = b ^ b0;
    // (* c = a * b *)
    // r0_01 = $distr;
    p0_01 = a0 * b1;
    r0_10 = r0_01 ^ p0_01;
    p0_10 = a1 * b0;
    r0_10 = r0_10 ^ p0_10;
    c0 = a0 * b0;
    int c0_1, c1_1, res;
    c0_1 = c0 ^ r0_01;
    c1 = a1 * b1;
    c1_1 = c1 ^ r0_10;
    res =  c0_1 ^ c1_1;
    return res;
  }
