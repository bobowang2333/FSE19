#include <stdio.h>

unsigned power(unsigned base, unsigned exp)
{
    unsigned result = 1;
    unsigned i;
    for(i = 0; i < exp; ++i)
        result *= base;
    return result;
}

int main(void)
{
    unsigned a, r1, r2, c, c1, c2;
    unsigned n = 6;
    unsigned op_left, op_right, res;
    printf("\t a \t r1 \t r2 \t c \t c1 \t c2   op_left   op_right  res \n");
    printf("Value %u\n", power(2,n));
    unsigned res_zero, res_one;
    res_zero = 0;
    res_one = 0;
    for (unsigned i = 0; i < power(2,n); ++i)
    {
        a =  (i >> 5) & 0x01;
        r1 = (i >> 4) & 0x01;
        r2 = (i >> 3) & 0x01;
        c = (i >> 2) & 0x01;
        c1 = (i >> 1) & 0x01;
        c2 = i & 0x01;
        op_left = ((((a & r1) ^ r2) & (c ^ c1)));
        op_right = (c1 & r2);
        res = op_left ^ op_right;
        if(!(i%4))
            printf("************************************************************************\n");
        printf("\t %u \t %u \t %u \t %u \t %u \t %u \t %u \t %u \t %u\n", a, r1, r2, c, c1, c2, op_left, op_right, res);
        if(!a) /* a == 0*/
            res_zero += res;
        else
            res_one += res;
    }
    printf("********Result(a = 0): %u, Result(a = 1): %u\n", res_zero, res_one);
    return 0;
}
