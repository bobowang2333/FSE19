//p3, Goublin unsignedean to arithmetic (bit0)
//for one bit operation subtraction, addition and xor are equivalent

/* original version */
// unsigned compute(unsigned R, unsigned rx, unsigned x){
unsigned compute(unsigned R, unsigned x, unsigned rx){
unsigned T1;
unsigned T2;
unsigned T3;
unsigned R2;
unsigned A1;
unsigned A2;
unsigned A3;
unsigned X;
 X = x ^ rx;
 T1 = X ^ R;
 T2 = T1 ^ R;
 T3 = T2 ^ X;
 R2 = R ^ rx;
 A1 = X ^ R2;
 A2 = A1 ^ R2;
 A3 = A2 ^ T3;
 return(A3);
} 
