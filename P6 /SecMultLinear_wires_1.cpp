#include <iostream>
  int SecMult(int a, int b, int a0, int r0_01, int p0_01){
    int a0, a1;
    int b0, b1;
    int t0, t0_prime, r0_01, r0_10, p0_01;
    // (* Presharing a *)
    a1 = a ^ a0;
    // (* b = a * (pow2 a) *)
    // t0 = pow2 p0_01;
    t0 = p0_01;
    t0 = a0 * t0;
    r0_10 = r0_01 ^ t0;
    // t0 = pow2 a0;
    t0 = a0;
    t0 = p0_01 * t0;
    r0_10 = r0_10 ^ t0;
    t0 = a1 ^ p0_01;
    // t0 = pow2 t0;
    t0 = a0 * t0;
    r0_10 = r0_10 ^ t0;
    // t0 = pow2 a0;
    t0 = a0;
    t0_prime = a1 ^ p0_01;
    t0 = t0_prime * t0;
    r0_10 = r0_10 ^ t0;
    t0 = a0 * a0; // pow2 a0;
    b0 = t0 ^ r0_01;
    t0 = a1 * a1; // pow2 a1;
    b1 = t0 ^ r0_10;
    return b0 ^ b1;
  }
