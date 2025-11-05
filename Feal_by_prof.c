/*
 * The FEAL cipher
 */

#include <stdio.h>

#define WORD32 unsigned int
#define BYTE   unsigned char

#define ROUNDS 4

#define ROT2(x) (((x)<<2) | ((x)>>6))

#define G0(a,b) (ROT2((BYTE)((a)+(b))))
#define G1(a,b) (ROT2((BYTE)((a)+(b)+1)))

static WORD32 pack32(BYTE *b)
{ /* pack 4 bytes into a 32-bit Word */
    return (WORD32)b[3]|((WORD32)b[2]<<8)|((WORD32)b[1]<<16)|((WORD32)b[0]<<24);
}

static void unpack32(WORD32 a,BYTE *b)
{ /* unpack bytes from a 32-bit word */
    b[0]=(BYTE)(a>>24);
    b[1]=(BYTE)(a>>16);
    b[2]=(BYTE)(a>>8);
    b[3]=(BYTE)a;
}

WORD32 f(WORD32 input)
{
    BYTE x[4],y[4];
    unpack32(input,x);
    y[1]=G1(x[1]^x[0],x[2]^x[3]);
    y[0]=G0(x[0],y[1]);
    y[2]=G0(y[1],x[2]^x[3]);
    y[3]=G1(y[2],x[3]);
    return pack32(y);
}

void encrypt(BYTE data[8],WORD32 key[6])
{
    WORD32 left,right,temp;

    left=pack32(&data[0]);
    right=left^pack32(&data[4]);
	
    for (int i=0;i<ROUNDS;i++)
    {
        temp=right;
        right=left^f(right^key[i]);
        left=temp;
    }
	
    temp=left;
    left=right^key[4];
    right=temp^right^key[5];
	
    unpack32(left,&data[0]);
    unpack32(right,&data[4]);
}

void decrypt(BYTE data[8],WORD32 key[6])
{
    WORD32 left,right,temp;
	
    right=pack32(&data[0])^key[4];
    left=right^pack32(&data[4])^key[5];
	
    for (int i=0;i<ROUNDS;i++)
    {
        temp=left;
        left=right^f(left^key[ROUNDS-1-i]);
        right=temp;
    }
	
    right^=left;
    
    unpack32(left,&data[0]);
    unpack32(right,&data[4]);
}


/* Not the key you are looking for!!! */
WORD32 key[6] = {
    0x63cab942,
    0x00a0c541,
    0x4674095a,
    0x64204c03,
    0x4b37d10a,
    0xd0a24877
};

int main(int argc,char **argv)
{
    BYTE data[8];
  
    argc--; argv++;
  
    if (argc!=8)
    {
        printf("command line error - input 8 bytes of plaintext in hex\n");
        printf("For example:-\n");
        printf("feal 01 23 45 67 89 ab cd ef\n");
        return 0;
    }
    for (int i=0;i<8;i++)
        sscanf(argv[i],"%hhx",&data[i]);

    printf("Plaintext=  ");
    for (int i=0;i<8;i++) printf("%02x",data[i]);
    printf("\n");

    encrypt(data,key);
    printf("Ciphertext= ");
    for (int i=0;i<8;i++) printf("%02x",data[i]);

    printf("\n");

    decrypt(data,key);
    printf("Plaintext=  ");
    for (int i=0;i<8;i++) printf("%02x",data[i]);
    printf("\n");

    return 0;
}
