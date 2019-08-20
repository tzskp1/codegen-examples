#include "MT.h"
#include <stdio.h>
#include <stdint.h>

int main(void) {
  init_genrand(20190820);
  int i;
  for (i = 0; i < 2048; ++i) {
    printf("%d:%u\n", i, (uint32_t)genrand_int32());
  }
  return 0;
}
