#include<stdio.h>
#include<string>
#include<math.h>
#include<fstream>
#include <bitset>
#include <iostream>
#include <cstdlib> // For system function
#include <sstream>
#include <vector>

using namespace std;


#define bitnum 5

#define SIZE (1 << bitnum)


string tobits(int num, int bit_num)
{
    string res="";

    for(int pos=0;pos<bit_num;pos++)
    {
        res=to_string(num%2)+res;
        num/=2;
    }

    return res;
}


int main(){
    int C,D;
    for(C = 0; C < 1; C++){ //C constrains the affine transformation of the S-box inputs.
        for(D = 0; D < 1; D++){ //D Constrains the affine transformation of the S-box outputs.
            int k = 13;
            FILE* fp = fopen("Model.cvc","w");

            fprintf(fp,"Counter_LAT : ARRAY  BITVECTOR(%d) OF BITVECTOR(1);\n", 3*bitnum);
            fprintf(fp,"Counter_DDT : ARRAY  BITVECTOR(%d) OF BITVECTOR(1);\n", 3*bitnum);
            fprintf(fp,"S : ARRAY  BITVECTOR(%d) OF BITVECTOR(%d);\n", bitnum, bitnum);

            //Variables in DDT
            for (int i = 0; i < SIZE; i++){
                for (int j = 0; j < SIZE - 1; j++){
                    fprintf(fp,"DDT_%d_%d , ",i,j);
                }
                fprintf(fp,"DDT_%d_%d : BITVECTOR(%d);\n", i, SIZE-1, bitnum+1);
            }
            fprintf(fp,"\n");

            //Variables in LAT
            for (int i = 0; i < SIZE; i++){
                for (int j = 0; j < SIZE - 1; j++){
                    fprintf(fp,"LAT_%d_%d , ",i,j);
                }
                fprintf(fp,"LAT_%d_%d : BITVECTOR(%d);\n", i, SIZE-1,bitnum+1);
            }
            fprintf(fp,"\n");


            //**SBox bijective
            for (int i = 0; i < SIZE; i++){
                for (int j = i + 1; j < SIZE; j++){
                    fprintf(fp,"ASSERT ( S[0h%x] /= S[0h%x] );\n",i,j);
                }
            }
            fprintf(fp,"\n");


            // no fix point
            for (int i = 0; i < SIZE; i++){
                fprintf(fp,"ASSERT ( S[0h%x] /= 0h%x );\n\n",i,i);
            }


            //**The count of each value in DDT
            for (int in = 0; in < SIZE; in++)
            {
                for (int out = 0; out < SIZE; out++)
                {
                    for (int x = 0; x < SIZE; x++)
                    {
                        fprintf(fp, "ASSERT ( IF S[ BVXOR( 0h%x , 0h%x )] = BVXOR( S[ 0h%x ] , 0h%x ) THEN Counter_DDT[0h%x%x%x] = 0bin1 ELSE Counter_DDT[0h%x%x%x] = 0bin0 ENDIF );\n", x, in, x, out, in, out, x, in, out, x); //S(x ^ Input D) = S(x) ^ Output D
                    }
                }
            }
            fprintf(fp, "\n");
            //***DDT counter
            for (int in = 0; in < SIZE; in++)
            {
                for (int out = 0; out < SIZE; out++)
                {
                    fprintf(fp, "ASSERT ( DDT_%d_%d = BVPLUS ( 5 ,", in, out);
                    for (int x = 0; x < SIZE; x++)
                    {
                        fprintf(fp, " 0bin0000@Counter_DDT[0h%x%x%x] ,", in, out, x);
                    }
                    fprintf(fp, " 0bin00000 ) );\n");
                }
            }
            fprintf(fp, "\n");

            //**The count of each value in LAT
            for (int in = 0; in < SIZE; in++ ) {
                for (int out = 0; out < SIZE; out++){
                    for ( int x = 0; x < SIZE; x++ ){
                        fprintf(fp,"ASSERT ( IF BVXOR ( 0h%x[0:0] & 0h%x[0:0] , BVXOR ( 0h%x[1:1] & 0h%x[1:1] , BVXOR ( 0h%x[2:2] & 0h%x[2:2] , 0h%x[3:3] & 0h%x[3:3] ) ) ) = BVXOR ( 0h%x[0:0] & S[0h%x][0:0] , BVXOR ( 0h%x[1:1] & S[0h%x][1:1] , BVXOR ( 0h%x[2:2] & S[0h%x][2:2] , 0h%x[3:3] & S[0h%x][3:3] ) ) ) THEN Counter_LAT[0h%x%x%x] = 0bin1 ELSE Counter_LAT[0h%x%x%x] = 0bin0 ENDIF );\n",in,x,in,x,in,x,in,x,out,x,out,x,out,x,out,x,in,out,x,in,out,x);//S(x ^ Input D) = S(x) ^ Output D
                    }

                }
            }
            fprintf(fp,"\n");
            //***LAT counter
            for (int in = 0; in < SIZE; in++ ) {
                for (int out = 0; out < SIZE; out++){
                    fprintf(fp,"ASSERT ( LAT_%d_%d = BVPLUS ( 5 ," ,in,out);
                    for ( int x = 0; x < SIZE; x++ ){
                        fprintf(fp," 0bin0000@Counter_LAT[0h%x%x%x] ,",in,out,x);
                    }
                    fprintf(fp," 0bin00000 ) );\n");
                }
            }
            fprintf(fp,"\n");


            //Restrictions of DDT and LAT
            //**DDT
            fprintf(fp,"ASSERT ( BVLE( DDT_0_1 , 0bin00100 )");
            for (int  out = 2; out < SIZE; out++) {
                fprintf(fp," AND BVLE( DDT_0_%d , 0bin00100 )",out );
            }
            for (int in = 1; in < SIZE ; in++ ) {
                for (int out = 0; out < SIZE; out++){
                    fprintf(fp," AND BVLE( DDT_%d_%d , 0bin00100 )",in,out );
                }
            }
            fprintf(fp," );\n\n" );

            //**LAT
            fprintf(fp,"ASSERT ( BVGE( LAT_0_1 , 0bin00100 ) AND BVLE( LAT_0_1 , 0bin01100 )");
            for (int  out = 2; out < SIZE; out++) {
                fprintf(fp," AND BVGE( LAT_0_%d , 0bin00100 ) AND BVLE( LAT_0_%d , 0bin01100 )",out,out );
            }
            for (int in = 1; in < SIZE ; in++ ) {
                for (int out = 0; out < SIZE; out++){
                    fprintf(fp," AND BVGE( LAT_%d_%d , 0bin00100 ) AND BVLE( LAT_%d_%d , 0bin01100 )",in,out,in,out);
                }
            }
            fprintf(fp," );\n\n" );


/***************************************************************************/
/***************************************************************************/


            // state variates

            //x: input of S-box
            for (int i = 0; i < SIZE * bitnum - 1; i++){
                fprintf(fp,"x_%d , ",i);
            }
            fprintf(fp,"x_%d : BITVECTOR(1);\n", SIZE * bitnum - 1);
            fprintf(fp,"\n");

            //y: output of S-box
            for (int i = 0; i < SIZE * bitnum - 1; i++){
                fprintf(fp,"y_%d , ",i);
            }
            fprintf(fp,"y_%d : BITVECTOR(1);\n", SIZE * bitnum - 1);
            fprintf(fp,"\n");

            //c
            for (int i = 0; i < SIZE * bitnum - 1; i++){
                fprintf(fp,"c_%d , ",i);
            }
            fprintf(fp,"c_%d : BITVECTOR(1);\n", SIZE * bitnum - 1);
            fprintf(fp,"\n");

            //d
            for (int i = 0; i < SIZE * bitnum - 1; i++){
                fprintf(fp,"d_%d , ",i);
            }
            fprintf(fp,"d_%d : BITVECTOR(1);\n", SIZE * bitnum - 1);
            fprintf(fp,"\n");

            //C,D
            fprintf(fp, "C,D : BITVECTOR(%d);\n", bitnum);
            fprintf(fp, "\n");



            //t: output of gates
            for (int i = 0; i < SIZE * k - 1; i++){
                fprintf(fp,"t_%d , ",i);
            }
            fprintf(fp,"t_%d : BITVECTOR(1);\n", SIZE * k - 1);
            fprintf(fp,"\n");

            //q: input of gates (3 times of t)
            for (int i = 0; i < SIZE * k * 3 - 1; i++){
                fprintf(fp,"q_%d , ",i);
            }
            fprintf(fp,"q_%d : BITVECTOR(1);\n", SIZE * k * 3 - 1);
            fprintf(fp,"\n");

            //a
            for (int i = 0; i < 3*k*bitnum + 1.5 * k*(k-1) + bitnum * bitnum + k * bitnum -1; i++){
                fprintf(fp,"a_%d , ",i);
            }
            fprintf(fp,"a_%d : BITVECTOR(1);\n", (3*k*bitnum + (3*k*(k-1))/2 + bitnum * bitnum + k * bitnum -1));
            fprintf(fp,"\n");

            //Depth
            for (int i = 0; i < k - 1 ; i++){
                fprintf(fp, "Dt_%d , ", i);
            }
            fprintf(fp, "Dt_%d : BITVECTOR(4);\n", k-1);
            fprintf(fp, "\n");

            //b: Controlling the type of each gate.
            for (int i = 0; i < 7 * k -1; i++){
                fprintf(fp,"b_%d , ",i);
            }
            fprintf(fp,"b_%d : BITVECTOR(1);\n", 7 * k -1);
            fprintf(fp,"\n");

            //B: The weight corresponding to the area of each gate.
            for (int i = 0; i < k-1; i ++ ){
                fprintf(fp,"B_%d , ",i);
            }
            fprintf(fp,"B_%d : BITVECTOR(8);\n",k-1);
            fprintf(fp, "\n");

            fprintf(fp,"GEC : BITVECTOR(8);\n");

            /***************************************************************************/
            /***************************************************************************/

            fprintf(fp, "ASSERT(C = 0bin%s);\n", tobits(C, bitnum).c_str());
            fprintf(fp, "ASSERT(D = 0bin%s);\n", tobits(D, bitnum).c_str());
            fprintf(fp, "\n");

            //Constraining the affine transformation of the S-box inputs.
            for(int i = 0 ; i < SIZE*bitnum; i+=bitnum){
                fprintf(fp,"ASSERT( c_%d",i);
                for(int j = 1; j < bitnum; j++ ){
                    fprintf(fp, "@c_%d", i+j);
                }
                fprintf(fp, " = BVXOR(C, x_%d", i);
                for(int j = 1; j < bitnum; j++){
                    fprintf(fp, "@x_%d", i+j);
                }
                fprintf(fp, "));\n");
            }
            fprintf(fp, "\n");

            //Constraining the affine transformation of the S-box outputs.
            for(int i = 0 ; i < SIZE*bitnum; i+=bitnum){
                fprintf(fp,"ASSERT( d_%d",i);
                for(int j = 1; j < bitnum; j++ ){
                    fprintf(fp, "@d_%d", i+j);
                }
                fprintf(fp, " = BVXOR(D, y_%d", i);
                for(int j = 1; j < bitnum; j++){
                    fprintf(fp, "@y_%d", i+j);
                }
                fprintf(fp, "));\n");
            }
            fprintf(fp, "\n");


            //constraint condition
            for (int i = 0; i < SIZE*bitnum; i+=bitnum) {
                fprintf(fp, "ASSERT( x_%d", i);
                for(int j = 1; j < bitnum; j++){
                    fprintf(fp, "@x_%d", i+j);
                }
                fprintf(fp, " = 0bin%s);\n", tobits(int(i/bitnum), bitnum).c_str());
            }
            fprintf(fp, "\n");

            //Sbox
            for (int i = 0; i < SIZE; i++){
                fprintf(fp,"ASSERT(  S[c_%d",i*bitnum);
                for (int j = 1; j < bitnum; j ++){
                    fprintf(fp,"@c_%d",i*bitnum+j);
                }
                fprintf(fp,"] =  ");

                fprintf(fp,"d_%d",i*bitnum);
                for (int j = 1; j < bitnum; j ++){
                    fprintf(fp,"@d_%d",i*bitnum+j);
                }
                fprintf(fp,");\n");
            }
            fprintf(fp, "\n");

            //LUT of S-box
            int sbox[32] = {0x0, 0x9, 0x12, 0xb, 0x5, 0xc, 0x16, 0xf, 0xa, 0x3, 0x18, 0x1, 0xd, 0x4, 0x1e, 0x7, 0x14, 0x15, 0x6, 0x17, 0x11, 0x10, 0x2, 0x13, 0x1a, 0x1b, 0x8, 0x19, 0x1d, 0x1c, 0xe, 0x1f };//KECCAK


            //Mapping the LUT values to each bit of the S-box output.
            for (int i = 0; i < (1 << bitnum); i++){
                fprintf(fp, "ASSERT(y_%d", bitnum*i);
                for(int j = 1; j < bitnum; j++){
                    fprintf(fp, " @ y_%d", bitnum*i+j);
                }
                fprintf(fp, " = 0bin%s);\n", tobits(sbox[i], bitnum).c_str());
            }
            fprintf(fp, "\n");

            //a
            int A_start = 0,
                    A_num = bitnum;
            for (int i = 0; i < k; i++)
            {
                for (int j = A_start ; j < A_start + A_num -1; j++){
                    for (int k = j + 1 ; k < A_start + A_num; k ++){
                        fprintf(fp,"ASSERT( a_%d & a_%d = 0bin0 );\n",j,k);
                    }
                }
                A_start += A_num;
                for (int j = A_start ; j < A_start + A_num -1; j++){
                    for (int k = j + 1 ; k < A_start + A_num; k ++){
                        fprintf(fp,"ASSERT( a_%d & a_%d = 0bin0 );\n",j,k);
                    }
                }
                A_start += A_num;
                for (int j = A_start ; j < A_start + A_num -1; j++){
                    for (int k = j + 1 ; k < A_start + A_num; k ++){
                        fprintf(fp,"ASSERT( a_%d & a_%d = 0bin0 );\n",j,k);
                    }
                }
                A_start += A_num;
                A_num++;
            }

            for (int i = 0; i < bitnum; i ++){
                for (int j = A_start ; j < A_start + A_num -1; j++){
                    for (int k = j + 1 ; k < A_start + A_num; k ++){
                        fprintf(fp,"ASSERT( a_%d & a_%d = 0bin0 );\n",j,k);
                    }
                }
                A_start += A_num ;
            }
            fprintf(fp,"\n");



            // Fixing the input order of logic gates.
            A_start = 0;
            A_num = bitnum;
            for(int i = 0; i < k; i++){
                for(int m = 0; m < 3-1; m++ ){
                    for(int n = m+1; n < 3; n++){
                        if(m == 3-2){
                            fprintf(fp, "ASSERT(IF(b_%d@b_%d@b_%d@b_%d@b_%d@b_%d@b_%d = 0bin0000011)THEN(a_%d", 7*i,7*i+1,7*i+2,7*i+3,7*i+4,7*i+5,7*i+6,A_start);
                            for(int a_q = A_start+1; a_q < A_start+A_num; a_q++){
                                fprintf(fp, "@a_%d", a_q);
                            }
                            for(int a_q = A_start + (n-m)*A_num; a_q < A_start + (n-m+1)*A_num; a_q++){
                                fprintf(fp, "@a_%d", a_q);
                            }
                            fprintf(fp, " = 0bin%s)ELSE(BVGT(a_%d", tobits(0, 2*A_num).c_str(), A_start);
                            for(int a_q = A_start+1; a_q < A_start+A_num; a_q++){
                                fprintf(fp, "@a_%d", a_q);
                            }
                            fprintf(fp, ", a_%d", A_start + (n-m)*A_num);
                            for(int a_q = A_start + (n-m)*A_num+1; a_q < A_start + (n-m+1)*A_num; a_q++){
                                fprintf(fp, "@a_%d", a_q);
                            }
                            fprintf(fp, "))ENDIF);\n");
                            fprintf(fp, "\n");
                        }

                        else{
                            fprintf(fp, "ASSERT(BVGT(a_%d", A_start);
                            for(int a_q = A_start+1; a_q < A_start+A_num; a_q++){
                                fprintf(fp, "@a_%d", a_q);
                            }
                            fprintf(fp, ", a_%d", A_start + (n-m)*A_num);
                            for(int a_q = A_start + (n-m)*A_num+1; a_q < A_start + (n-m+1)*A_num; a_q++){
                                fprintf(fp, "@a_%d", a_q);
                            }
                            fprintf(fp, "));\n");
                        }

                    }
                    A_start += A_num;
                }
                A_start += A_num;
                A_num++;
            }

            //Fixing the order of output of S-box.
            for(int i = 0; i < bitnum-1; i++){
                for (int j = i+1; j < bitnum; j++){
                    fprintf(fp, "ASSERT(BVGT(a_%d", A_start);
                    for(int a_y = A_start+1; a_y < A_start+A_num; a_y++){
                        fprintf(fp, "@a_%d", a_y);
                    }
                    fprintf(fp, ", a_%d", A_start + (j-i)*A_num);
                    for(int a_y = A_start + (j-i)*A_num +1; a_y < A_start + (j-i+1)*A_num; a_y++){
                        fprintf(fp, "@a_%d", a_y);
                    }
                    fprintf(fp, "));\n");
                }
                A_start += A_num;
            }
            fprintf(fp, "\n");


            //The gates directly connected to the S-box output are linear gates.
            A_start = 0;
            A_num = bitnum;
            for(int i = 0; i < k; i++){
                A_start += 3*A_num;
                A_num++;
            }
            for(int i = 0; i < bitnum; i++){
                for(int j = 0; j < k; j++) {
                    fprintf(fp, "ASSERT((a_%d = 0bin1) => (BVGE(B_%d, 0bin00000110)));\n", A_start + bitnum + j, j);
                }
                A_start = A_start + bitnum + k;
            }
            fprintf(fp, "\n");



            A_start = 0;
            A_num = bitnum;
            for (int i = 0; i < k; i++) // k gates
            {
                fprintf(fp,"ASSERT( BVLE( BVPLUS( 2 ");
                for(int j = A_start ; j < A_start + A_num; j++){
                    fprintf(fp,",0bin0@a_%d ",j);
                }
                fprintf(fp,"), 0bin01));\n");
                A_start += A_num;
                fprintf(fp,"ASSERT( BVLE( BVPLUS( 2 ");
                for(int j = A_start ; j < A_start + A_num; j++){
                    fprintf(fp,",0bin0@a_%d ",j);
                }
                fprintf(fp,"), 0bin01));\n");
                A_start += A_num;
                fprintf(fp,"ASSERT( BVLE( BVPLUS( 2 ");
                for(int j = A_start ; j < A_start + A_num; j++){
                    fprintf(fp,",0bin0@a_%d ",j);
                }
                fprintf(fp,"), 0bin01));\n");
                A_start += A_num;
                A_num++;
            }

            for (int i = 0; i < bitnum; i ++){
                fprintf(fp,"ASSERT( BVLE(0bin01 , BVPLUS( 2 ");
                for(int j = A_start ; j < A_start + A_num; j++){
                    fprintf(fp,",0bin0@a_%d ",j);
                }
                fprintf(fp,")));\n");
                A_start += A_num;
            }
            fprintf(fp,"\n");




            int countQ = 0, countT = 0, countY = 0, countX = 0;
            //q & t &d
            for (int i = 0; i < SIZE; i++){
                int countA=0,countB=0,T=countT;
                //q & t
                for (int j = 0; j < k; j++){
                    //first q
                    fprintf(fp,"ASSERT( q_%d = ",countQ++);

                    for (int h = 0; h < bitnum; h ++){
                        fprintf(fp,"BVXOR( a_%d & c_%d , ",countA++,countX+h);
                    }

                    for (int g = T; g < countT - 1; g ++ ){
                        fprintf(fp,"BVXOR( a_%d & t_%d , ",countA++,g);
                    }
                    if (countT - T > 0){
                        fprintf(fp,"a_%d & t_%d ",countA++,countT-1);
                    }
                    else {
                        fprintf(fp,"0bin0 ) ");
                    }

                    //fill up brackets
                    for (int g = 0; g < bitnum+countT-1-T; g++){
                        fprintf(fp,") ");
                    }
                    fprintf(fp,");\n");

                    //second q
                    fprintf(fp,"ASSERT( q_%d = ",countQ++);

                    for (int h = 0; h < bitnum; h ++){
                        fprintf(fp,"BVXOR( a_%d & c_%d , ",countA++,countX+h);
                    }

                    for (int g = T; g < countT - 1; g ++ ){
                        fprintf(fp,"BVXOR( a_%d & t_%d , ",countA++,g);
                    }
                    if (countT - T > 0){
                        fprintf(fp,"a_%d & t_%d ",countA++,countT-1);
                    }
                    else {
                        fprintf(fp,"0bin0 ) ");
                    }

                    //fill up bracket
                    for (int g = 0; g < bitnum+countT-1-T; g++){
                        fprintf(fp,") ");
                    }
                    fprintf(fp,");\n");

                    //third q
                    fprintf(fp,"ASSERT( q_%d = ",countQ++);

                    for (int h = 0; h < bitnum; h ++){
                        fprintf(fp,"BVXOR( a_%d & c_%d , ",countA++,countX+h);
                    }

                    for (int g = T; g < countT - 1; g ++ ){
                        fprintf(fp,"BVXOR( a_%d & t_%d , ",countA++,g);
                    }
                    if (countT - T > 0){
                        fprintf(fp,"a_%d & t_%d ",countA++,countT-1);
                    }
                    else {
                        fprintf(fp,"0bin0 ) ");
                    }

                    //fill up bracket
                    for (int g = 0; g < bitnum+countT-1-T; g++){
                        fprintf(fp,") ");
                    }
                    fprintf(fp,");\n");

                    //The expression that represents the relationship between the inputs and outputs of logic gates.
                    //fprintf(fp,"ASSERT( t_%d =  BVXOR( b_%d & q_%d & q_%d , BVXOR( b_%d & q_%d , BVXOR( b_%d & q_%d , b_%d ) ) ) );\n",countT++,countB,countQ-2,countQ-1,countB+1,countQ-2,countB+1,countQ-1,countB+2);
                    fprintf(fp, "ASSERT( t_%d = BVXOR(b_%d & q_%d & q_%d & q_%d, BVXOR(b_%d & q_%d & q_%d, BVXOR(b_%d & q_%d & q_%d, BVXOR(b_%d & q_%d & q_%d, BVXOR(b_%d & q_%d, BVXOR(b_%d & q_%d, BVXOR(b_%d & q_%d, BVXOR(b_%d & q_%d, BVXOR(b_%d & q_%d, BVXOR(b_%d & q_%d, BVXOR(b_%d & q_%d & q_%d, BVXOR(b_%d & q_%d, BVXOR(b_%d & q_%d, BVXOR(b_%d & q_%d, b_%d)))))))))))))));\n", countT++, countB,countQ-3,countQ-2,countQ-1, countB+1,countQ-3,countQ-2, countB+1,countQ-3,countQ-1, countB+1,countQ-2,countQ-1, countB+1,countQ-3, countB+1,countQ-2, countB+1,countQ-1, countB+2,countQ-3, countB+2,countQ-2, countB+2,countQ-1, countB+3,countQ-3,countQ-2, countB+4,countQ-3, countB+4,countQ-2, countB+5,countQ-3, countB+6);
                    //fprintf(fp, "ASSERT( t_%d = BVXOR(b_%d & q_%d & q_%d & q_%d & q_%d, BVXOR(b_%d & q_%d & q_%d & q_%d, BVXOR(b_%d & q_%d & q_%d & q_%d, BVXOR(b_%d & q_%d & q_%d, BVXOR(b_%d & q_%d, BVXOR(b_%d & q_%d, BVXOR(b_%d & q_%d & q_%d & q_%d, BVXOR(b_%d & q_%d & q_%d, BVXOR(b_%d & q_%d & q_%d, BVXOR(b_%d & q_%d & q_%d, BVXOR(b_%d & q_%d, BVXOR(b_%d & q_%d, BVXOR(b_%d & q_%d, BVXOR(b_%d & q_%d, BVXOR(b_%d & q_%d, BVXOR(b_%d & q_%d, BVXOR(b_%d & q_%d & q_%d, BVXOR(b_%d & q_%d, BVXOR(b_%d & q_%d, BVXOR(b_%d & q_%d, b_%d)))))))))))))))))))));\n",countT++, countB,countQ-4,countQ-3,countQ-2,countQ-1, countB,countQ-4,countQ-3,countQ-2, countB,countQ-4,countQ-3,countQ-1, countB,countQ-2,countQ-1, countB,countQ-2, countB,countQ-1, countB+1,countQ-4,countQ-3,countQ-2, countB+2,countQ-4,countQ-3, countB+2,countQ-4,countQ-2, countB+2,countQ-3,countQ-2, countB+2,countQ-4, countB+2,countQ-3, countB+2,countQ-2, countB+3,countQ-4, countB+3,countQ-3, countB+3,countQ-2, countB+4,countQ-4,countQ-3, countB+5,countQ-4, countB+5,countQ-3, countB+6,countQ-4, countB+7);
                    countB += 7;
                }

                //y
                for (int j = 0; j < bitnum; j++ ){
                    fprintf(fp,"ASSERT( d_%d = ",countY++);
                    for (int h = 0; h < bitnum; h ++){
                        fprintf(fp,"BVXOR( a_%d & c_%d , ",countA++,countX+h);
                    }

                    for (int g = T; g < countT - 1; g ++ ){
                        fprintf(fp,"BVXOR( a_%d & t_%d , ",countA++,g);
                    }
                    if (countT - T > 0){
                        fprintf(fp,"a_%d & t_%d ",countA++,countT-1);
                    }

                    //fill up bracket
                    for (int g = 0; g < bitnum+countT-1-T; g++){
                        fprintf(fp,") ");
                    }
                    fprintf(fp,");\n");

                }
                fprintf(fp,"\n");
                countX+=bitnum;
            }


            const int ROWS = 16;
            const int COLS_Degree3 = 4;
            const int COLS_Degree2 = 6;

            //g_u(x) for cubic terms
            int matrixDegree3[ROWS][COLS_Degree3] = {
                    {1,1,1,1},
                    {0,1,1,1},
                    {1,0,1,1},
                    {0,0,1,1},
                    {1,1,0,1},
                    {0,1,0,1},
                    {1,0,0,1},
                    {0,0,0,1},
                    {1,1,1,0},
                    {0,1,1,0},
                    {1,0,1,0},
                    {0,0,1,0},
                    {1,1,0,0},
                    {0,1,0,0},
                    {1,0,0,0},
                    {0,0,0,0}
            };

            //g_u(x) for quadratic terms
            int matrixDegree2[ROWS][COLS_Degree2] = {
                    {1,1,1,1,1,1},
                    {0,0,1,0,1,1},
                    {0,1,0,1,0,1},
                    {0,0,0,0,0,1},
                    {1,0,0,1,1,0},
                    {0,0,0,0,1,0},
                    {0,0,0,1,0,0},
                    {0,0,0,0,0,0},
                    {1,1,1,0,0,0},
                    {0,0,1,0,0,0},
                    {0,1,0,0,0,0},
                    {0,0,0,0,0,0},
                    {1,0,0,0,0,0},
                    {0,0,0,0,0,0},
                    {0,0,0,0,0,0},
                    {0,0,0,0,0,0}
            };


            // Constraining the algebraic degree of every coordinate function of S-box is 2.
            for (int m = 0; m < bitnum; m++){
                fprintf(fp, "ASSERT(BVGT(");
                for (int i = 0; i < 6; i++){
                    fprintf(fp, "BVPLUS(1, 0bin0");
                    for(int j = 0; j < SIZE; j++){
                        fprintf(fp, ", (d_%d & 0bin%d)", 4 * j + m, matrixDegree2[j][i]);
                    }
                    if (i == (6-1)){
                        fprintf(fp, "), 0bin000000));\n");
                    }else{
                        fprintf(fp, ") @ ");
                    }
                }
            }
            fprintf(fp, "\n");



            //Constraining the algebraic degree of the S-box is 3.
            for (int m = 0; m < bitnum; m++) {
                fprintf(fp, "ASSERT(BVGT(");
                for (int i = 0; i < 4; i++) {
                    fprintf(fp, "BVPLUS(1, 0bin0");
                    for (int j = 0; j < SIZE; j++) {
                        fprintf(fp, ", (d_%d & 0bin%d)", 4 * j + m, matrixDegree3[j][i]);
                    }
                    if (m == bitnum - 1 && i == (4 - 1) ) {
                        fprintf(fp, "), 0bin0000000000000000));\n");
                    } else {
                        fprintf(fp, ") @ ");
                    }
                }
            }
            fprintf(fp, "\n");

            //Constraining the algebraic degree of every coordinate function of S-box is 3.
            for (int m = 0; m < bitnum; m++){
                fprintf(fp, "ASSERT(BVGT(");
                for (int i = 0; i < 4; i++){
                    fprintf(fp, "BVPLUS(1, 0bin0");
                    for(int j = 0; j < SIZE; j++){
                        fprintf(fp, ", (d_%d & 0bin%d)", 4 * j + m, matrixDegree3[j][i]);
                    }
                    if (i == (4-1)){
                        fprintf(fp, "), 0bin0000));\n");
                    }else{
                        fprintf(fp, ") @ ");
                    }
                }
            }
            fprintf(fp, "\n");


            //The encoding of gates constrained by b and their correspoding area.
            for (int i = 0; i < k; i++ ){
//                fprintf (fp,"ASSERT( (b_%d@b_%d@b_%d@b_%d@b_%d@b_%d@b_%d@b_%d = 0bin00000011) => ( B_%d = 0bin00000010) );\n",8*i,8*i+1,8*i+2,8*i+3,8*i+4,8*i+5,8*i+6,8*i+7,i);//~(q0)
//                fprintf (fp,"ASSERT( (b_%d@b_%d@b_%d@b_%d@b_%d@b_%d@b_%d@b_%d = 0bin00000100) => ( B_%d = 0bin00001000) );\n",8*i,8*i+1,8*i+2,8*i+3,8*i+4,8*i+5,8*i+6,8*i+7,i);//XOR(MAOI)
//                fprintf (fp,"ASSERT( (b_%d@b_%d@b_%d@b_%d@b_%d@b_%d@b_%d@b_%d = 0bin00000101) => ( B_%d = 0bin00000110) );\n",8*i,8*i+1,8*i+2,8*i+3,8*i+4,8*i+5,8*i+6,8*i+7,i);//XNOR(MOAI)
//                fprintf (fp,"ASSERT( (b_%d@b_%d@b_%d@b_%d@b_%d@b_%d@b_%d@b_%d = 0bin00000111) => ( B_%d = 0bin00000010) );\n",8*i,8*i+1,8*i+2,8*i+3,8*i+4,8*i+5,8*i+6,8*i+7,i);//~(q1)
//                fprintf (fp,"ASSERT( (b_%d@b_%d@b_%d@b_%d@b_%d@b_%d@b_%d@b_%d = 0bin00001000) => ( B_%d = 0bin00000100) );\n",8*i,8*i+1,8*i+2,8*i+3,8*i+4,8*i+5,8*i+6,8*i+7,i);//AND
//                fprintf (fp,"ASSERT( (b_%d@b_%d@b_%d@b_%d@b_%d@b_%d@b_%d@b_%d = 0bin00001001) => ( B_%d = 0bin00000011) );\n",8*i,8*i+1,8*i+2,8*i+3,8*i+4,8*i+5,8*i+6,8*i+7,i);//NAND
//                fprintf (fp,"ASSERT( (b_%d@b_%d@b_%d@b_%d@b_%d@b_%d@b_%d@b_%d = 0bin00001100) => ( B_%d = 0bin00000100) );\n",8*i,8*i+1,8*i+2,8*i+3,8*i+4,8*i+5,8*i+6,8*i+7,i);//OR
//                fprintf (fp,"ASSERT( (b_%d@b_%d@b_%d@b_%d@b_%d@b_%d@b_%d@b_%d = 0bin00001101) => ( B_%d = 0bin00000011) );\n",8*i,8*i+1,8*i+2,8*i+3,8*i+4,8*i+5,8*i+6,8*i+7,i);//NOR
//                fprintf (fp,"ASSERT( (b_%d@b_%d@b_%d@b_%d@b_%d@b_%d@b_%d@b_%d = 0bin01000000) => ( B_%d = 0bin00000101) );\n",8*i,8*i+1,8*i+2,8*i+3,8*i+4,8*i+5,8*i+6,8*i+7,i);//AND3
//                fprintf (fp,"ASSERT( (b_%d@b_%d@b_%d@b_%d@b_%d@b_%d@b_%d@b_%d = 0bin01000001) => ( B_%d = 0bin00000100) );\n",8*i,8*i+1,8*i+2,8*i+3,8*i+4,8*i+5,8*i+6,8*i+7,i);//NAND3
//                fprintf (fp,"ASSERT( (b_%d@b_%d@b_%d@b_%d@b_%d@b_%d@b_%d@b_%d = 0bin01100000) => ( B_%d = 0bin00000101) );\n",8*i,8*i+1,8*i+2,8*i+3,8*i+4,8*i+5,8*i+6,8*i+7,i);//OR3
//                fprintf (fp,"ASSERT( (b_%d@b_%d@b_%d@b_%d@b_%d@b_%d@b_%d@b_%d = 0bin01100001) => ( B_%d = 0bin00000100) );\n",8*i,8*i+1,8*i+2,8*i+3,8*i+4,8*i+5,8*i+6,8*i+7,i);//NOR3
//                fprintf (fp,"ASSERT( (b_%d@b_%d@b_%d@b_%d@b_%d@b_%d@b_%d@b_%d = 0bin00010000) => ( B_%d = 0bin00001110) );\n",8*i,8*i+1,8*i+2,8*i+3,8*i+4,8*i+5,8*i+6,8*i+7,i);//XOR3
//                fprintf (fp,"ASSERT( (b_%d@b_%d@b_%d@b_%d@b_%d@b_%d@b_%d@b_%d = 0bin00010001) => ( B_%d = 0bin00001110) );\n",8*i,8*i+1,8*i+2,8*i+3,8*i+4,8*i+5,8*i+6,8*i+7,i);//XNOR3
//                fprintf (fp,"ASSERT( (b_%d@b_%d@b_%d@b_%d@b_%d@b_%d@b_%d@b_%d = 0bin10000000) => ( B_%d = 0bin00001000) );\n",8*i,8*i+1,8*i+2,8*i+3,8*i+4,8*i+5,8*i+6,8*i+7,i);//MAOI
//                fprintf (fp,"ASSERT( (b_%d@b_%d@b_%d@b_%d@b_%d@b_%d@b_%d@b_%d = 0bin10000001) => ( B_%d = 0bin00000110) );\n",8*i,8*i+1,8*i+2,8*i+3,8*i+4,8*i+5,8*i+6,8*i+7,i);//MOAI
//                fprintf(fp, "\n");

                fprintf(fp, "ASSERT( (b_%d@b_%d@b_%d@b_%d@b_%d@b_%d@b_%d = 0bin0000011) => (B_%d = 0bin00000010) );\n", 7*i, 7*i+1, 7*i+2, 7*i+3, 7*i+4, 7*i+5, 7*i+6, i); //~(q0)
                fprintf(fp, "ASSERT( (b_%d@b_%d@b_%d@b_%d@b_%d@b_%d@b_%d = 0bin0000100) => (B_%d = 0bin00001000) );\n", 7*i, 7*i+1, 7*i+2, 7*i+3, 7*i+4, 7*i+5, 7*i+6, i); //XOR
                fprintf(fp, "ASSERT( (b_%d@b_%d@b_%d@b_%d@b_%d@b_%d@b_%d = 0bin0000101) => (B_%d = 0bin00000110) );\n", 7*i, 7*i+1, 7*i+2, 7*i+3, 7*i+4, 7*i+5, 7*i+6, i); //XNOR
                fprintf(fp, "ASSERT( (b_%d@b_%d@b_%d@b_%d@b_%d@b_%d@b_%d = 0bin0000111) => (B_%d = 0bin00000010) );\n", 7*i, 7*i+1, 7*i+2, 7*i+3, 7*i+4, 7*i+5, 7*i+6, i); //~(q1)
                fprintf(fp, "ASSERT( (b_%d@b_%d@b_%d@b_%d@b_%d@b_%d@b_%d = 0bin0001000) => (B_%d = 0bin00000100) );\n", 7*i, 7*i+1, 7*i+2, 7*i+3, 7*i+4, 7*i+5, 7*i+6, i); //AND
                fprintf(fp, "ASSERT( (b_%d@b_%d@b_%d@b_%d@b_%d@b_%d@b_%d = 0bin0001001) => (B_%d = 0bin00000011) );\n", 7*i, 7*i+1, 7*i+2, 7*i+3, 7*i+4, 7*i+5, 7*i+6, i); //NAND
                fprintf(fp, "ASSERT( (b_%d@b_%d@b_%d@b_%d@b_%d@b_%d@b_%d = 0bin0001100) => (B_%d = 0bin00000100) );\n", 7*i, 7*i+1, 7*i+2, 7*i+3, 7*i+4, 7*i+5, 7*i+6, i); //OR
                fprintf(fp, "ASSERT( (b_%d@b_%d@b_%d@b_%d@b_%d@b_%d@b_%d = 0bin0001101) => (B_%d = 0bin00000011) );\n", 7*i, 7*i+1, 7*i+2, 7*i+3, 7*i+4, 7*i+5, 7*i+6, i); //NOR
                fprintf(fp, "ASSERT( (b_%d@b_%d@b_%d@b_%d@b_%d@b_%d@b_%d = 0bin1000000) => (B_%d = 0bin00000101) );\n", 7*i, 7*i+1, 7*i+2, 7*i+3, 7*i+4, 7*i+5, 7*i+6, i); //AND3
                fprintf(fp, "ASSERT( (b_%d@b_%d@b_%d@b_%d@b_%d@b_%d@b_%d = 0bin1000001) => (B_%d = 0bin00000100) );\n", 7*i, 7*i+1, 7*i+2, 7*i+3, 7*i+4, 7*i+5, 7*i+6, i); //NAND3
                fprintf(fp, "ASSERT( (b_%d@b_%d@b_%d@b_%d@b_%d@b_%d@b_%d = 0bin1100000) => (B_%d = 0bin00000101) );\n", 7*i, 7*i+1, 7*i+2, 7*i+3, 7*i+4, 7*i+5, 7*i+6, i); //OR3
                fprintf(fp, "ASSERT( (b_%d@b_%d@b_%d@b_%d@b_%d@b_%d@b_%d = 0bin1100001) => (B_%d = 0bin00000100) );\n", 7*i, 7*i+1, 7*i+2, 7*i+3, 7*i+4, 7*i+5, 7*i+6, i); //NOR3
                fprintf(fp, "ASSERT( (b_%d@b_%d@b_%d@b_%d@b_%d@b_%d@b_%d = 0bin0010000) => (B_%d = 0bin00001110) );\n", 7*i, 7*i+1, 7*i+2, 7*i+3, 7*i+4, 7*i+5, 7*i+6, i); //XOR3
                fprintf(fp, "ASSERT( (b_%d@b_%d@b_%d@b_%d@b_%d@b_%d@b_%d = 0bin0010001) => (B_%d = 0bin00001110) );\n", 7*i, 7*i+1, 7*i+2, 7*i+3, 7*i+4, 7*i+5, 7*i+6, i); //XNOR3
                fprintf(fp, "\n");

                fprintf(fp, "ASSERT(BVGE(b_%d@b_%d@b_%d@b_%d@b_%d@b_%d@b_%d, 0bin0000011));\n",7*i,7*i+1,7*i+2,7*i+3,7*i+4,7*i+5,7*i+6);
                fprintf(fp, "ASSERT(NOT(b_%d@b_%d@b_%d@b_%d@b_%d@b_%d@b_%d = 0bin0000110));\n",7*i,7*i+1,7*i+2,7*i+3,7*i+4,7*i+5,7*i+6);
                fprintf(fp, "ASSERT(NOT(b_%d@b_%d@b_%d@b_%d@b_%d@b_%d@b_%d = 0bin0001010));\n",7*i,7*i+1,7*i+2,7*i+3,7*i+4,7*i+5,7*i+6);
                fprintf(fp, "ASSERT(NOT(b_%d@b_%d@b_%d@b_%d@b_%d@b_%d@b_%d = 0bin0001011));\n",7*i,7*i+1,7*i+2,7*i+3,7*i+4,7*i+5,7*i+6);
                fprintf(fp, "ASSERT(NOT(b_%d@b_%d@b_%d@b_%d@b_%d@b_%d@b_%d = 0bin0001110));\n",7*i,7*i+1,7*i+2,7*i+3,7*i+4,7*i+5,7*i+6);
                fprintf(fp, "ASSERT(NOT(b_%d@b_%d@b_%d@b_%d@b_%d@b_%d@b_%d = 0bin0001111));\n",7*i,7*i+1,7*i+2,7*i+3,7*i+4,7*i+5,7*i+6);
                fprintf(fp, "ASSERT((b_%d = 0bin1) => (b_%d@b_%d@b_%d@b_%d@b_%d = 0bin00000));\n", 7*i+2, 7*i, 7*i+1, 7*i+3, 7*i+4, 7*i+5);
                fprintf(fp, "ASSERT((b_%d = 0bin1) => (b_%d@b_%d@b_%d@b_%d = 0bin0000));\n", 7*i, 7*i+2, 7*i+3, 7*i+4, 7*i+5);
                fprintf(fp, "ASSERT(NOT(b_%d@b_%d = 0bin01));\n", 7*i, 7*i+1);
                fprintf(fp, "\n");
            }
            fprintf(fp, "\n");
            fprintf(fp, "\n");



            for(int i = 0; i < k; i++){
                fprintf(fp, "ASSERT(BVGT(B_%d, 0bin00000000));\n", i);
            }
            fprintf(fp, "\n");


            fprintf(fp,"ASSERT( GEC = BVPLUS( 8 , ");
            for (int i = 0; i < k; i++){
                fprintf(fp,"B_%d , ",i);
            }
            fprintf(fp," 0bin00000000 ) );\n\n");



            //Constraining the area of whole circuit implementation.
            fprintf(fp,"ASSERT( GEC = 0bin00101011   );\n");
            fprintf(fp, "\n");

            //end

            fprintf(fp,"QUERY(FALSE);\nCOUNTEREXAMPLE;\n");
            fclose(fp);


        }
    }


    return 0;

}
