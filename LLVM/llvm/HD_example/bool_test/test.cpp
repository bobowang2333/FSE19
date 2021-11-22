#include <stdio.h>
#include <stdint.h>
bool compute(bool r1, bool r2, bool k1, bool k2, bool p1)
{
    bool c1;
    bool c2;
    bool c3;
    bool c4;
    c1 = r1 ^ k1;
    c2 = r2 ^ k2;
    c3 = p1 & c1;
    c4 = c3 | c2;
    return c4;
}

