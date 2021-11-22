#include <stdio.h>
#include <stdlib.h>

int leak(int i1, int i2, int key, int i3)
{
    int n1, n2, n3;
    n1 = i1 ^ i2;
    n2 = n1 ^ 1 ^ key;
    n3 = n2 & i3;
    return n3;
}

int main()
{
    int i1, i2, i3, i4, res;
    i1 = 1;
    i2 = 0;
    i3 = 0;
    i4 = 1;
    res = leak(i1, i2, i3, i4);
    return res;
}
