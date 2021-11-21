//p2, Messerges boolean to arithmetic (bit0)
//for one bit operation subtraction, addition and xor are equivalent
bool compute(bool C, bool rx, bool x){
    bool B;
    bool A1;
    bool A2;
    bool A3;
    bool A4;
    bool X;
    X = x ^ rx;
    B = C ^ rx;
    A1 = C ^ X;
    A2 = A1 ^ B;
    A3 = A2 ^ C;
    A4 = A3 ^ C;
    return(A4);
}
