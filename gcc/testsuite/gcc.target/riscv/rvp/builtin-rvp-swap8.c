/* This is a test program for wsbh instruction.  */
/* { dg-do run { target { riscv32*-*-* } } } */
/* { dg-options "-O0" } */

#include <rvp_intrinsic.h>
#include <stdlib.h>
#include <stdint.h>

#if defined(__riscv_zpn) && !defined(__riscv_32e)
int
main ()
{
  uint32_t a = 0x03020100;
  uint32_t b;

  b = __rv__swap8 (a);

  if (b != 0x02030001)
    abort ();
  else
    exit (0);
}
#else
int main(){return 0;}
#endif
