#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <ctype.h>

char state_buffer[256];

void setSeed(unsigned int seed)
{
  initstate(seed, state_buffer, sizeof(state_buffer));
}

unsigned int getRandom()
{
  long int r = random();
  return (unsigned int) r;
}
