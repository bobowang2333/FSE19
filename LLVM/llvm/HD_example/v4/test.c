#include <stdio.h>
#include <stdlib.h>

void leak(int *i1, int *i2)
{
    *i1 = *i1 ^ *i2;
}

int main()
{
    int i1, i2;
    i1 = 1;
    i2 = 0;
    leak(&i1, &i2);
    return 0;
}

