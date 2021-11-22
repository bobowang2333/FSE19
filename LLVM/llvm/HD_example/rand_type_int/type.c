#include <stdio.h>
#include <stdint.h>
int compute(int r1, int r2, int r3, int k)
{
    int c1,c2,c3,c4,c5,c6;
    c1 = k ^ r2;
    c2 = r1 ^ r2;
    c3 = c2 ^ c1;
    c4 = c3 ^ c2;
    c5 = c4 ^ r1;
    c6 = c5 & r3;
    return c6;
}
