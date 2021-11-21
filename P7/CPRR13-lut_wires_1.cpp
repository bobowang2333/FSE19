int CPRR13_lut_wires_1(int x, int x0, int r1_01, int p1_01, int r2_01, int p2_01, int r3_01, int r4_01){
    var x1;
    var r0, r1;
    var z0_0, z0_1, w0_0, w0_1, t1, r1_10, t2, r2_10, r3_10, p3_01, p3_10, r4_10, p4_01, p4_10;
    // (* Presharing x *)
    x1 = x ^ x0;
    // (* r = SBox[x] *)
    // (* r = exp x 254 *)
    // (* z0 = exp x 2 *)
    // z0_0 = pow2 x0;
    z0_0 = x0;
    // z0_1 = pow2 x1;
    z0_1 = x1;
    // (* r = x * (pow2 x) *)
    t1 = x0 ^ p1_01;
    // t1 = lut2 t1;
    r1_10 = r1_01 ^ t1;
    t1 = x1 ^ p1_01;
    // t1 = lut2 t1;
    r1_10 = r1_10 ^ t1;
    t1 = x0 ^ p1_01;
    t1 = t1 ^ x1;
    // t1 = lut2 t1;
    r1_10 = r1_10 ^ t1;
    // t1 = lut2 p1_01;
    t1 = p1_01;
    r1_10 = r1_10 ^ t1;
    // r0 = lut2 x0;
    r0 = x0;
    r0 = r0 ^ r1_01;
    // r1 = lut2 x1;
    r1 = x1;
    r1 = r1 ^ r1_10;
    // (* w0 = exp x 4 *)
    // w0_0 = pow4 r0;
    w0_0 = r0;
    // w0_1 = pow4 r1;
    w0_1 = r1;
    // (* r = r * (pow4 r) *)
    t2 = r0 ^ p2_01;
    // t2 = lut4 t2;
    r2_10 = r2_01 ^ t2;
    t2 = r1 ^ p2_01;
    // t2 = lut4 t2;
    r2_10 = r2_10 ^ t2;
    t2 = r0 ^ p2_01;
    t2 = t2 ^ r1;
    // t2 = lut4 t2;
    r2_10 = r2_10 ^ t2;
    // t2 = lut4 p2_01;
    t2 = p2_01;
    r2_10 = r2_10 ^ t2;
    // r0 = lut4 r0;
    r0 = r0 ^ r2_01;
    // r1 = lut4 r1;
    r1 = r1 ^ r2_10;
    // (* r0 = exp r 16 *)
    // r0 = pow16 r0;
    // r1 = pow16 r1;
    // (* r = r * w0_ *)
    p3_01 = r0 * w0_1;
    r3_10 = r3_01 ^ p3_01;
    p3_10 = r1 * w0_0;
    r3_10 = r3_10 ^ p3_10;
    r0 = r0 * w0_0;
    r0 = r0 ^ r3_01;
    r1 = r1 * w0_1;
    r1 = r1 ^ r3_10;
    // (* r = r * z0_ *)
    p4_01 = r0 * z0_1;
    r4_10 = r4_01 ^ p4_01;
    p4_10 = r1 * z0_0;
    r4_10 = r4_10 ^ p4_10;
    r0 = r0 * z0_0;
    r0 = r0 ^ r4_01;
    r1 = r1 * z0_1;
    r1 = r1 ^ r4_10;
    // (* r = affineF r *)
    // r0 = affineF r0;
    // r1 = affineF r1;
    r0 = r0 ^ Ox51;
    return r0 ^ r1;
  }

