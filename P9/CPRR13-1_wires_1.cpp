#include <iostream>

uint8_t CPRR13_wires(uint8_t x, uint8_t x0, uint8_t r1_01, uint8_t p1_01, uint8_t r2_01, uint8_t p2_01, uint8_t r3_01, uint8_t r4_01)
{
    uint8_t x1;
    uint8_t r0, r1;
    uint8_t z0_0, z0_1, w0_0, w0_1, t1, t1_prime, r1_10, t2, t2_prime, r2_10, r3_10, p3_01, p3_10, r4_10, p4_01, p4_10;
    x1 = x ^ x0;
    z0_0 = x0;
    z0_1 = x1;
    // t1 = pow2 p1_01;
    t1 = p1_01;
    t1 = x0 * t1;
    r1_10 = r1_01 ^ t1;
    // t1 = pow2 x0;
    t1 = x0;
    t1 = p1_01 * t1;
    r1_10 = r1_10 ^ t1;
    t1 = x1 ^ p1_01;
    // t1 = pow2 t1;
    t1 = t1;
    t1 = x0 * t1;
    r1_10 = r1_10 ^ t1;
    // t1 = pow2 x0;
    t1 = x0;
    t1_prime = x1 ^ p1_01;
    t1 = t1_prime * t1;
    r1_10 = r1_10 ^ t1;
    t1 = x0 * x0; //pow2 x0;
    r0 = t1 ^ r1_01;
    t1 = x1 * x1; //pow2 x1;
    r1 = t1 ^ r1_10;
    // (* w0 = exp x 4 *)
    // w0_0 = pow4 r0;
    w0_0 = r0;
    // w0_1 = pow4 r1;
    w0_1 = r1;
    // t2 = pow4 p2_01;
    t2 = p2_01;
    t2 = r0 * t2;
    r2_10 = r2_01 ^ t2;
    // t2 = pow4 r0;
    t2 = r0;
    t2 = p2_01 * t2;
    r2_10 = r2_10 ^ t2;
    t2 = r1 ^ p2_01;
    // t2 = pow4 t2;
    t2 = r0 * t2;
    r2_10 = r2_10 ^ t2;
    // t2 = pow4 r0;
    t2 = r0;
    t2_prime = r1 ^ p2_01;
    t2 = t2_prime * t2;
    r2_10 = r2_10 ^ t2;
    t2 = r0 * r0; //pow4 r0;
    r0 = t2 ^ r2_01;
    t2 = r1 * r1; //pow4 r1;
    r1 = t2 ^ r2_10;
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
    // r4_01 = $distr;
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

